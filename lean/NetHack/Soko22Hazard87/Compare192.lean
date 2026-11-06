import NetHack.Soko22Hazard87.Compare191
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48000 (p : Pattern) (guard : d370094 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370094, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d370094, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370093 p = 1 := by simpa only [d370094, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47999 p hg
    simpa only [d370094, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48001 (p : Pattern) (guard : d370095 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d370095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370094 p = 1 := by simpa only [d370095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48000 p hg
    simpa only [d370095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48002 (p : Pattern) (guard : d370096 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d370084 p = 1 := by simpa only [d370096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47990 p hg
    simpa only [d370096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370095 p = 1 := by simpa only [d370096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48001 p hg
    simpa only [d370096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48003 (p : Pattern) (guard : d370097 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370096 p = 1 := by simpa only [d370097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48002 p hg
    simpa only [d370097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d370097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48004 (p : Pattern) (guard : d370098 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d370097 p = 1 := by simpa only [d370098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48003 p hg
    simpa only [d370098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d370098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48005 (p : Pattern) (guard : d370099 p = 1) : d50822 p ≤ (1 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d370098 p = 1 := by simpa only [d370099, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48004 p hg
    simpa only [d370099, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370099, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46827 p hg
    simpa only [d370099, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48006 (p : Pattern) (guard : d370100 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d370014 p = 1 := by simpa only [d370100, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47905 p hg
    simpa only [d370100, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370099 p = 1 := by simpa only [d370100, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48005 p hg
    simpa only [d370100, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48007 (p : Pattern) (guard : d370101 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370100 p = 1 := by simpa only [d370101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48006 p hg
    simpa only [d370101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48008 (p : Pattern) (guard : d370102 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370101 p = 1 := by simpa only [d370102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48007 p hg
    simpa only [d370102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48009 (p : Pattern) (guard : d370103 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370102 p = 1 := by simpa only [d370103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48008 p hg
    simpa only [d370103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48010 (p : Pattern) (guard : d370104 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370103 p = 1 := by simpa only [d370104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48009 p hg
    simpa only [d370104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48011 (p : Pattern) (guard : d370105 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370104 p = 1 := by simpa only [d370105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48010 p hg
    simpa only [d370105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48012 (p : Pattern) (guard : d370106 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370105 p = 1 := by simpa only [d370106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48011 p hg
    simpa only [d370106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48013 (p : Pattern) (guard : d370107 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370106 p = 1 := by simpa only [d370107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48012 p hg
    simpa only [d370107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48014 (p : Pattern) (guard : d370108 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370107 p = 1 := by simpa only [d370108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48013 p hg
    simpa only [d370108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48015 (p : Pattern) (guard : d370109 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d369854 p = 1 := by simpa only [d370109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47667 p hg
    simpa only [d370109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370108 p = 1 := by simpa only [d370109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48014 p hg
    simpa only [d370109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48016 (p : Pattern) (guard : d370424 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d370109 p = 1 := by simpa only [d370424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48015 p hg
    simpa only [d370424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48017 (p : Pattern) (guard : d370425 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d370424 p = 1 := by simpa only [d370425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48016 p hg
    simpa only [d370425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48018 (p : Pattern) (guard : d370426 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 260 with
  | false =>
    have hg : d370425 p = 1 := by simpa only [d370426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48017 p hg
    simpa only [d370426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48019 (p : Pattern) (guard : d370427 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 259 with
  | false =>
    have hg : d370426 p = 1 := by simpa only [d370427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48018 p hg
    simpa only [d370427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48020 (p : Pattern) (guard : d370428 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 258 with
  | false =>
    have hg : d370427 p = 1 := by simpa only [d370428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48019 p hg
    simpa only [d370428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48021 (p : Pattern) (guard : d370429 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 257 with
  | false =>
    have hg : d370428 p = 1 := by simpa only [d370429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48020 p hg
    simpa only [d370429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48022 (p : Pattern) (guard : d370430 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 256 with
  | false =>
    have hg : d370429 p = 1 := by simpa only [d370430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48021 p hg
    simpa only [d370430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48023 (p : Pattern) (guard : d370431 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 255 with
  | false =>
    have hg : d370430 p = 1 := by simpa only [d370431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48022 p hg
    simpa only [d370431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48024 (p : Pattern) (guard : d370432 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 254 with
  | false =>
    have hg : d370431 p = 1 := by simpa only [d370432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48023 p hg
    simpa only [d370432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48025 (p : Pattern) (guard : d370433 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 253 with
  | false =>
    have hg : d370432 p = 1 := by simpa only [d370433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48024 p hg
    simpa only [d370433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48026 (p : Pattern) (guard : d370434 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 252 with
  | false =>
    have hg : d370433 p = 1 := by simpa only [d370434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48025 p hg
    simpa only [d370434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48027 (p : Pattern) (guard : d370435 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 251 with
  | false =>
    have hg : d370434 p = 1 := by simpa only [d370435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48026 p hg
    simpa only [d370435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48028 (p : Pattern) (guard : d370436 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 250 with
  | false =>
    have hg : d370435 p = 1 := by simpa only [d370436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48027 p hg
    simpa only [d370436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48029 (p : Pattern) (guard : d370437 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 249 with
  | false =>
    have hg : d370436 p = 1 := by simpa only [d370437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48028 p hg
    simpa only [d370437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48030 (p : Pattern) (guard : d370438 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 245 with
  | false =>
    have hg : d370437 p = 1 := by simpa only [d370438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48029 p hg
    simpa only [d370438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48031 (p : Pattern) (guard : d370439 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 200 with
  | false =>
    have hg : d370438 p = 1 := by simpa only [d370439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48030 p hg
    simpa only [d370439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48032 (p : Pattern) (guard : d370440 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 199 with
  | false =>
    have hg : d370439 p = 1 := by simpa only [d370440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48031 p hg
    simpa only [d370440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48033 (p : Pattern) (guard : d370441 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 186 with
  | false =>
    have hg : d370440 p = 1 := by simpa only [d370441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48032 p hg
    simpa only [d370441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48034 (p : Pattern) (guard : d370442 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 185 with
  | false =>
    have hg : d370441 p = 1 := by simpa only [d370442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48033 p hg
    simpa only [d370442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48035 (p : Pattern) (guard : d370443 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 184 with
  | false =>
    have hg : d370442 p = 1 := by simpa only [d370443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48034 p hg
    simpa only [d370443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48036 (p : Pattern) (guard : d370444 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 181 with
  | false =>
    have hg : d370443 p = 1 := by simpa only [d370444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48035 p hg
    simpa only [d370444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48037 (p : Pattern) (guard : d370445 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 177 with
  | false =>
    have hg : d370444 p = 1 := by simpa only [d370445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48036 p hg
    simpa only [d370445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48038 (p : Pattern) (guard : d370446 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 164 with
  | false =>
    have hg : d370445 p = 1 := by simpa only [d370446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48037 p hg
    simpa only [d370446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48039 (p : Pattern) (guard : d370447 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 156 with
  | false =>
    have hg : d370446 p = 1 := by simpa only [d370447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48038 p hg
    simpa only [d370447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48040 (p : Pattern) (guard : d370448 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 155 with
  | false =>
    have hg : d370447 p = 1 := by simpa only [d370448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48039 p hg
    simpa only [d370448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48041 (p : Pattern) (guard : d370449 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 134 with
  | false =>
    have hg : d370448 p = 1 := by simpa only [d370449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48040 p hg
    simpa only [d370449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48042 (p : Pattern) (guard : d370450 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 133 with
  | false =>
    have hg : d370449 p = 1 := by simpa only [d370450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48041 p hg
    simpa only [d370450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48043 (p : Pattern) (guard : d370451 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 120 with
  | false =>
    have hg : d370450 p = 1 := by simpa only [d370451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48042 p hg
    simpa only [d370451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48044 (p : Pattern) (guard : d370452 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 118 with
  | false =>
    have hg : d370451 p = 1 := by simpa only [d370452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d370452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48045 (p : Pattern) (guard : d370453 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 114 with
  | false =>
    have hg : d370452 p = 1 := by simpa only [d370453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48044 p hg
    simpa only [d370453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48046 (p : Pattern) (guard : d370454 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 111 with
  | false =>
    have hg : d370453 p = 1 := by simpa only [d370454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48045 p hg
    simpa only [d370454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48047 (p : Pattern) (guard : d370455 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 98 with
  | false =>
    have hg : d370454 p = 1 := by simpa only [d370455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48046 p hg
    simpa only [d370455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48048 (p : Pattern) (guard : d370456 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 97 with
  | false =>
    have hg : d370455 p = 1 := by simpa only [d370456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48047 p hg
    simpa only [d370456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48049 (p : Pattern) (guard : d370457 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 94 with
  | false =>
    have hg : d370456 p = 1 := by simpa only [d370457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48048 p hg
    simpa only [d370457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48050 (p : Pattern) (guard : d370458 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 76 with
  | false =>
    have hg : d370457 p = 1 := by simpa only [d370458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48049 p hg
    simpa only [d370458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48051 (p : Pattern) (guard : d370459 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 67 with
  | false =>
    have hg : d370458 p = 1 := by simpa only [d370459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48050 p hg
    simpa only [d370459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48052 (p : Pattern) (guard : d370460 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 52 with
  | false =>
    have hg : d370459 p = 1 := by simpa only [d370460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48051 p hg
    simpa only [d370460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48053 (p : Pattern) (guard : d370461 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 47 with
  | false =>
    have hg : d370460 p = 1 := by simpa only [d370461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48052 p hg
    simpa only [d370461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48054 (p : Pattern) (guard : d370462 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 46 with
  | false =>
    have hg : d370461 p = 1 := by simpa only [d370462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48053 p hg
    simpa only [d370462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48055 (p : Pattern) (guard : d370463 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 45 with
  | false =>
    have hg : d370462 p = 1 := by simpa only [d370463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48054 p hg
    simpa only [d370463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48056 (p : Pattern) (guard : d370464 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 30 with
  | false =>
    have hg : d370463 p = 1 := by simpa only [d370464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48055 p hg
    simpa only [d370464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48057 (p : Pattern) (guard : d370465 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 29 with
  | false =>
    have hg : d370464 p = 1 := by simpa only [d370465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48056 p hg
    simpa only [d370465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48058 (p : Pattern) (guard : d370466 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 28 with
  | false =>
    have hg : d370465 p = 1 := by simpa only [d370466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48057 p hg
    simpa only [d370466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48059 (p : Pattern) (guard : d370467 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 27 with
  | false =>
    have hg : d370466 p = 1 := by simpa only [d370467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48058 p hg
    simpa only [d370467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48060 (p : Pattern) (guard : d370468 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 25 with
  | false =>
    have hg : d370467 p = 1 := by simpa only [d370468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48059 p hg
    simpa only [d370468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d370468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48061 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48062 (p : Pattern) (guard : d0 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48063 (p : Pattern) (guard : d0 p = 1) : d50588 p ≤ (0 : Int) + d367817 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48064 (p : Pattern) (guard : d0 p = 1) : d50546 p ≤ (0 : Int) + d367788 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48065 (p : Pattern) (guard : d0 p = 1) : d50566 p ≤ (0 : Int) + d367798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48066 (p : Pattern) (guard : d0 p = 1) : d50569 p ≤ (0 : Int) + d367800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48067 (p : Pattern) (guard : d45587 p = 1) : d47617 p ≤ (0 : Int) + d47617 p := by
  omega
theorem compare48068 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (0 : Int) + d49391 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48069 (p : Pattern) (guard : d46472 p = 1) : d47617 p ≤ (0 : Int) + d49392 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48067 p hg
    simpa only [d46472, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48068 p hg
    simpa only [d46472, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48070 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (0 : Int) + d49395 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48071 (p : Pattern) (guard : d46473 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46472 p = 1 := by simpa only [d46473, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48069 p hg
    simpa only [d46473, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46473, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48070 p hg
    simpa only [d46473, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48072 (p : Pattern) (guard : d46477 p = 1) : d47617 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46473 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48071 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48073 (p : Pattern) (guard : d0 p = 1) : d49396 p ≤ (0 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48074 (p : Pattern) (guard : d179204 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46477 p = 1 := by simpa only [d179204, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48072 p hg
    simpa only [d179204, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179204, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48073 p hg
    simpa only [d179204, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48075 (p : Pattern) (guard : d275501 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d179204 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48074 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48076 (p : Pattern) (guard : d275502 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d275501 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48075 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48077 (p : Pattern) (guard : d0 p = 1) : d49397 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48078 (p : Pattern) (guard : d275503 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d275502 p = 1 := by simpa only [d275503, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48076 p hg
    simpa only [d275503, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275503, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48077 p hg
    simpa only [d275503, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48079 (p : Pattern) (guard : d0 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48080 (p : Pattern) (guard : d275504 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d275503 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48078 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48079 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48081 (p : Pattern) (guard : d0 p = 1) : d50527 p ≤ (0 : Int) + d367774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48082 (p : Pattern) (guard : d275505 p = 1) : d50570 p ≤ (0 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d275504 p = 1 := by simpa only [d275505, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48080 p hg
    simpa only [d275505, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275505, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d275505, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48083 (p : Pattern) (guard : d0 p = 1) : d50531 p ≤ (0 : Int) + d367777 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48084 (p : Pattern) (guard : d275506 p = 1) : d50571 p ≤ (0 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d275505 p = 1 := by simpa only [d275506, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48082 p hg
    simpa only [d275506, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275506, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d275506, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48085 (p : Pattern) (guard : d275507 p = 1) : d50572 p ≤ (0 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275507, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d275507, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275506 p = 1 := by simpa only [d275507, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48084 p hg
    simpa only [d275507, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48086 (p : Pattern) (guard : d0 p = 1) : d50575 p ≤ (0 : Int) + d367804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48087 (p : Pattern) (guard : d275508 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d275507 p = 1 := by simpa only [d275508, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48085 p hg
    simpa only [d275508, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275508, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d275508, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48088 (p : Pattern) (guard : d0 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48089 (p : Pattern) (guard : d275509 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d275508 p = 1 := by simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48087 p hg
    simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48088 p hg
    simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48090 (p : Pattern) (guard : d275510 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d275509 p = 1 := by simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48089 p hg
    simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48088 p hg
    simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48091 (p : Pattern) (guard : d275511 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d275510 p = 1 := by simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48090 p hg
    simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48088 p hg
    simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48092 (p : Pattern) (guard : d275512 p = 1) : d50577 p ≤ (0 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275512, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48065 p hg
    simpa only [d275512, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275511 p = 1 := by simpa only [d275512, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48091 p hg
    simpa only [d275512, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48093 (p : Pattern) (guard : d275513 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275513, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48064 p hg
    simpa only [d275513, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275512 p = 1 := by simpa only [d275513, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48092 p hg
    simpa only [d275513, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48094 (p : Pattern) (guard : d0 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48095 (p : Pattern) (guard : d275514 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d275513 p = 1 := by simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48093 p hg
    simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48096 (p : Pattern) (guard : d275515 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d275514 p = 1 := by simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48095 p hg
    simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48097 (p : Pattern) (guard : d275516 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d275515 p = 1 := by simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48096 p hg
    simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48098 (p : Pattern) (guard : d0 p = 1) : d50589 p ≤ (0 : Int) + d367818 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48099 (p : Pattern) (guard : d275517 p = 1) : d50590 p ≤ (0 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d275516 p = 1 := by simpa only [d275517, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48097 p hg
    simpa only [d275517, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275517, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48098 p hg
    simpa only [d275517, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48100 (p : Pattern) (guard : d275518 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275518, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d275518, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275517 p = 1 := by simpa only [d275518, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48099 p hg
    simpa only [d275518, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48101 (p : Pattern) (guard : d275519 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d275518 p = 1 := by simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48100 p hg
    simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48102 (p : Pattern) (guard : d275520 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d275519 p = 1 := by simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48101 p hg
    simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48103 (p : Pattern) (guard : d275521 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d275520 p = 1 := by simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48102 p hg
    simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48104 (p : Pattern) (guard : d275522 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275521 p = 1 := by simpa only [d275522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48103 p hg
    simpa only [d275522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48105 (p : Pattern) (guard : d275523 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275522 p = 1 := by simpa only [d275523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48104 p hg
    simpa only [d275523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48106 (p : Pattern) (guard : d275581 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275523 p = 1 := by simpa only [d275581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48105 p hg
    simpa only [d275581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48107 (p : Pattern) (guard : d275582 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275581 p = 1 := by simpa only [d275582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48106 p hg
    simpa only [d275582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48108 (p : Pattern) (guard : d275583 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275582 p = 1 := by simpa only [d275583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48107 p hg
    simpa only [d275583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48109 (p : Pattern) (guard : d275584 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275583 p = 1 := by simpa only [d275584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48108 p hg
    simpa only [d275584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48110 (p : Pattern) (guard : d275585 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275584 p = 1 := by simpa only [d275585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48109 p hg
    simpa only [d275585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48111 (p : Pattern) (guard : d275529 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d275521 p = 1 := by simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48103 p hg
    simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48112 (p : Pattern) (guard : d275530 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275529 p = 1 := by simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48111 p hg
    simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48113 (p : Pattern) (guard : d275588 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275530 p = 1 := by simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48112 p hg
    simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48114 (p : Pattern) (guard : d275589 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275588 p = 1 := by simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48113 p hg
    simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48115 (p : Pattern) (guard : d275590 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275589 p = 1 := by simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48114 p hg
    simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48116 (p : Pattern) (guard : d275591 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275590 p = 1 := by simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48115 p hg
    simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48117 (p : Pattern) (guard : d275592 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d275584 p = 1 := by simpa only [d275592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48109 p hg
    simpa only [d275592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275591 p = 1 := by simpa only [d275592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48116 p hg
    simpa only [d275592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48118 (p : Pattern) (guard : d275593 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d275585 p = 1 := by simpa only [d275593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48110 p hg
    simpa only [d275593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275592 p = 1 := by simpa only [d275593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48117 p hg
    simpa only [d275593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48119 (p : Pattern) (guard : d275594 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d275593 p = 1 := by simpa only [d275594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48118 p hg
    simpa only [d275594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48120 (p : Pattern) (guard : d277223 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d275594 p = 1 := by simpa only [d277223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48119 p hg
    simpa only [d277223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d277223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d277223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48121 (p : Pattern) (guard : d277224 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d277224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d277224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277223 p = 1 := by simpa only [d277224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48120 p hg
    simpa only [d277224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48122 (p : Pattern) (guard : d0 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48123 (p : Pattern) (guard : d0 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48124 (p : Pattern) (guard : d0 p = 1) : d50671 p ≤ (0 : Int) + d367875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48125 (p : Pattern) (guard : d0 p = 1) : d50631 p ≤ (0 : Int) + d367850 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48126 (p : Pattern) (guard : d0 p = 1) : d50653 p ≤ (0 : Int) + d367860 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48127 (p : Pattern) (guard : d0 p = 1) : d50656 p ≤ (0 : Int) + d367862 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48128 (p : Pattern) (guard : d45587 p = 1) : d47706 p ≤ (0 : Int) + d47706 p := by
  omega
theorem compare48129 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (0 : Int) + d49560 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48130 (p : Pattern) (guard : d46472 p = 1) : d47706 p ≤ (0 : Int) + d49561 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48128 p hg
    simpa only [d46472, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48129 p hg
    simpa only [d46472, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48131 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (0 : Int) + d49564 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48132 (p : Pattern) (guard : d46473 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46472 p = 1 := by simpa only [d46473, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48130 p hg
    simpa only [d46473, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46473, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48131 p hg
    simpa only [d46473, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48133 (p : Pattern) (guard : d46477 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46473 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48132 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48134 (p : Pattern) (guard : d0 p = 1) : d49565 p ≤ (0 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48135 (p : Pattern) (guard : d179204 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46477 p = 1 := by simpa only [d179204, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48133 p hg
    simpa only [d179204, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179204, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48134 p hg
    simpa only [d179204, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48136 (p : Pattern) (guard : d275501 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d179204 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48135 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48137 (p : Pattern) (guard : d275502 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d275501 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48136 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48138 (p : Pattern) (guard : d0 p = 1) : d49566 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48139 (p : Pattern) (guard : d275503 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d275502 p = 1 := by simpa only [d275503, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48137 p hg
    simpa only [d275503, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275503, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48138 p hg
    simpa only [d275503, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48140 (p : Pattern) (guard : d0 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48141 (p : Pattern) (guard : d275504 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d275503 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48139 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48140 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48142 (p : Pattern) (guard : d0 p = 1) : d50530 p ≤ (0 : Int) + d367776 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48143 (p : Pattern) (guard : d275505 p = 1) : d50657 p ≤ (0 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d275504 p = 1 := by simpa only [d275505, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48141 p hg
    simpa only [d275505, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275505, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d275505, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48144 (p : Pattern) (guard : d275506 p = 1) : d50658 p ≤ (0 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d275505 p = 1 := by simpa only [d275506, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48143 p hg
    simpa only [d275506, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275506, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d275506, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48145 (p : Pattern) (guard : d275507 p = 1) : d50659 p ≤ (0 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275507, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d275507, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275506 p = 1 := by simpa only [d275507, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48144 p hg
    simpa only [d275507, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48146 (p : Pattern) (guard : d0 p = 1) : d50662 p ≤ (0 : Int) + d367866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48147 (p : Pattern) (guard : d275508 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d275507 p = 1 := by simpa only [d275508, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48145 p hg
    simpa only [d275508, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275508, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d275508, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48148 (p : Pattern) (guard : d0 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48149 (p : Pattern) (guard : d275509 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d275508 p = 1 := by simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48147 p hg
    simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48148 p hg
    simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48150 (p : Pattern) (guard : d275510 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d275509 p = 1 := by simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48149 p hg
    simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48148 p hg
    simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48151 (p : Pattern) (guard : d275511 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d275510 p = 1 := by simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48150 p hg
    simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48148 p hg
    simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48152 (p : Pattern) (guard : d275512 p = 1) : d50664 p ≤ (0 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275512, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48126 p hg
    simpa only [d275512, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275511 p = 1 := by simpa only [d275512, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48151 p hg
    simpa only [d275512, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48153 (p : Pattern) (guard : d275513 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275513, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48125 p hg
    simpa only [d275513, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275512 p = 1 := by simpa only [d275513, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48152 p hg
    simpa only [d275513, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48154 (p : Pattern) (guard : d0 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48155 (p : Pattern) (guard : d275514 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d275513 p = 1 := by simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48153 p hg
    simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48156 (p : Pattern) (guard : d275515 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d275514 p = 1 := by simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48155 p hg
    simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48157 (p : Pattern) (guard : d275516 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d275515 p = 1 := by simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48156 p hg
    simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48158 (p : Pattern) (guard : d0 p = 1) : d50672 p ≤ (0 : Int) + d367876 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48159 (p : Pattern) (guard : d275517 p = 1) : d50673 p ≤ (0 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d275516 p = 1 := by simpa only [d275517, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48157 p hg
    simpa only [d275517, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275517, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48158 p hg
    simpa only [d275517, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48160 (p : Pattern) (guard : d275518 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275518, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48124 p hg
    simpa only [d275518, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275517 p = 1 := by simpa only [d275518, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48159 p hg
    simpa only [d275518, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48161 (p : Pattern) (guard : d275519 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d275518 p = 1 := by simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48160 p hg
    simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48162 (p : Pattern) (guard : d275520 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d275519 p = 1 := by simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48161 p hg
    simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48163 (p : Pattern) (guard : d275521 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d275520 p = 1 := by simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48162 p hg
    simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48164 (p : Pattern) (guard : d275529 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d275521 p = 1 := by simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48163 p hg
    simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48165 (p : Pattern) (guard : d275530 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275529 p = 1 := by simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48164 p hg
    simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48166 (p : Pattern) (guard : d275588 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275530 p = 1 := by simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48165 p hg
    simpa only [d275588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48167 (p : Pattern) (guard : d275589 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275588 p = 1 := by simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48166 p hg
    simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48168 (p : Pattern) (guard : d275590 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275589 p = 1 := by simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48167 p hg
    simpa only [d275590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48169 (p : Pattern) (guard : d275591 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275590 p = 1 := by simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48168 p hg
    simpa only [d275591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48170 (p : Pattern) (guard : d275820 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275820, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275820, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275591 p = 1 := by simpa only [d275820, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48169 p hg
    simpa only [d275820, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48171 (p : Pattern) (guard : d275821 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d275821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275820 p = 1 := by simpa only [d275821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48170 p hg
    simpa only [d275821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48172 (p : Pattern) (guard : d277225 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d275821 p = 1 := by simpa only [d277225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48171 p hg
    simpa only [d277225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d277225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d277225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48173 (p : Pattern) (guard : d277226 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d277225 p = 1 := by simpa only [d277226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48172 p hg
    simpa only [d277226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d277226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d277226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48174 (p : Pattern) (guard : d277227 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d277226 p = 1 := by simpa only [d277227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48173 p hg
    simpa only [d277227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d277227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d277227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48175 (p : Pattern) (guard : d277228 p = 1) : d50676 p ≤ (0 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d277224 p = 1 := by simpa only [d277228, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48121 p hg
    simpa only [d277228, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277227 p = 1 := by simpa only [d277228, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48174 p hg
    simpa only [d277228, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48176 (p : Pattern) (guard : d0 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48177 (p : Pattern) (guard : d0 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48178 (p : Pattern) (guard : d0 p = 1) : d50712 p ≤ (0 : Int) + d367901 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48179 (p : Pattern) (guard : d0 p = 1) : d50724 p ≤ (0 : Int) + d367910 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48180 (p : Pattern) (guard : d0 p = 1) : d50725 p ≤ (0 : Int) + d367780 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48181 (p : Pattern) (guard : d45587 p = 1) : d47630 p ≤ (0 : Int) + d47630 p := by
  omega
theorem compare48182 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (0 : Int) + d49310 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48183 (p : Pattern) (guard : d46472 p = 1) : d47630 p ≤ (0 : Int) + d49311 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48181 p hg
    simpa only [d46472, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48182 p hg
    simpa only [d46472, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48184 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (0 : Int) + d49315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48185 (p : Pattern) (guard : d46473 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46472 p = 1 := by simpa only [d46473, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48183 p hg
    simpa only [d46473, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46473, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48184 p hg
    simpa only [d46473, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48186 (p : Pattern) (guard : d46477 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46473 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48185 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48187 (p : Pattern) (guard : d0 p = 1) : d49316 p ≤ (0 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48188 (p : Pattern) (guard : d179204 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46477 p = 1 := by simpa only [d179204, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48186 p hg
    simpa only [d179204, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179204, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48187 p hg
    simpa only [d179204, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48189 (p : Pattern) (guard : d275501 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d179204 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48188 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48190 (p : Pattern) (guard : d275502 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d275501 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48189 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48191 (p : Pattern) (guard : d0 p = 1) : d49317 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48192 (p : Pattern) (guard : d275503 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d275502 p = 1 := by simpa only [d275503, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48190 p hg
    simpa only [d275503, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275503, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48191 p hg
    simpa only [d275503, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48193 (p : Pattern) (guard : d0 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48194 (p : Pattern) (guard : d275504 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d275503 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48192 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48193 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48195 (p : Pattern) (guard : d275546 p = 1) : d50726 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275546, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d275546, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275504 p = 1 := by simpa only [d275546, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48194 p hg
    simpa only [d275546, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48196 (p : Pattern) (guard : d275505 p = 1) : d50727 p ≤ (0 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d275504 p = 1 := by simpa only [d275505, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48080 p hg
    simpa only [d275505, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275505, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d275505, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48197 (p : Pattern) (guard : d275547 p = 1) : d50728 p ≤ (0 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d275546 p = 1 := by simpa only [d275547, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48195 p hg
    simpa only [d275547, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275505 p = 1 := by simpa only [d275547, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48196 p hg
    simpa only [d275547, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48198 (p : Pattern) (guard : d45587 p = 1) : d47634 p ≤ (0 : Int) + d47634 p := by
  omega
theorem compare48199 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (0 : Int) + d47963 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48200 (p : Pattern) (guard : d46472 p = 1) : d47634 p ≤ (0 : Int) + d49319 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48198 p hg
    simpa only [d46472, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48199 p hg
    simpa only [d46472, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48201 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (0 : Int) + d49322 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48202 (p : Pattern) (guard : d46473 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46472 p = 1 := by simpa only [d46473, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48200 p hg
    simpa only [d46473, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46473, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48201 p hg
    simpa only [d46473, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48203 (p : Pattern) (guard : d46477 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46473 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48202 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48204 (p : Pattern) (guard : d0 p = 1) : d49323 p ≤ (0 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48205 (p : Pattern) (guard : d179204 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46477 p = 1 := by simpa only [d179204, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48203 p hg
    simpa only [d179204, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179204, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48204 p hg
    simpa only [d179204, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48206 (p : Pattern) (guard : d275501 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d179204 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48205 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48207 (p : Pattern) (guard : d275502 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d275501 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48206 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48208 (p : Pattern) (guard : d0 p = 1) : d49324 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48209 (p : Pattern) (guard : d275503 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d275502 p = 1 := by simpa only [d275503, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48207 p hg
    simpa only [d275503, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275503, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48208 p hg
    simpa only [d275503, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48210 (p : Pattern) (guard : d0 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48211 (p : Pattern) (guard : d275504 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d275503 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48209 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48210 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48212 (p : Pattern) (guard : d275505 p = 1) : d50573 p ≤ (0 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d275504 p = 1 := by simpa only [d275505, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48211 p hg
    simpa only [d275505, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275505, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d275505, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48213 (p : Pattern) (guard : d275506 p = 1) : d50574 p ≤ (0 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d275505 p = 1 := by simpa only [d275506, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48212 p hg
    simpa only [d275506, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275506, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d275506, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48214 (p : Pattern) (guard : d275548 p = 1) : d50729 p ≤ (0 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d275547 p = 1 := by simpa only [d275548, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48197 p hg
    simpa only [d275548, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275506 p = 1 := by simpa only [d275548, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48213 p hg
    simpa only [d275548, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48215 (p : Pattern) (guard : d0 p = 1) : d50732 p ≤ (0 : Int) + d367916 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48216 (p : Pattern) (guard : d275549 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d275548 p = 1 := by simpa only [d275549, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48214 p hg
    simpa only [d275549, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275549, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d275549, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48217 (p : Pattern) (guard : d0 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48218 (p : Pattern) (guard : d275550 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d275549 p = 1 := by simpa only [d275550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48216 p hg
    simpa only [d275550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48217 p hg
    simpa only [d275550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48219 (p : Pattern) (guard : d275551 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d275550 p = 1 := by simpa only [d275551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48218 p hg
    simpa only [d275551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48217 p hg
    simpa only [d275551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48220 (p : Pattern) (guard : d275552 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d275551 p = 1 := by simpa only [d275552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48219 p hg
    simpa only [d275552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48217 p hg
    simpa only [d275552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48221 (p : Pattern) (guard : d275553 p = 1) : d50734 p ≤ (0 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275553, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48179 p hg
    simpa only [d275553, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275552 p = 1 := by simpa only [d275553, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48220 p hg
    simpa only [d275553, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48222 (p : Pattern) (guard : d275554 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275554, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48178 p hg
    simpa only [d275554, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275553 p = 1 := by simpa only [d275554, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48221 p hg
    simpa only [d275554, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48223 (p : Pattern) (guard : d0 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48224 (p : Pattern) (guard : d275555 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d275554 p = 1 := by simpa only [d275555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48222 p hg
    simpa only [d275555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d275555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48225 (p : Pattern) (guard : d275556 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d275555 p = 1 := by simpa only [d275556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48224 p hg
    simpa only [d275556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d275556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48226 (p : Pattern) (guard : d275557 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d275556 p = 1 := by simpa only [d275557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48225 p hg
    simpa only [d275557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d275557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48227 (p : Pattern) (guard : d0 p = 1) : d50736 p ≤ (0 : Int) + d367920 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48228 (p : Pattern) (guard : d275558 p = 1) : d50737 p ≤ (0 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d275557 p = 1 := by simpa only [d275558, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48226 p hg
    simpa only [d275558, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275558, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48227 p hg
    simpa only [d275558, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48229 (p : Pattern) (guard : d275559 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275559, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d275559, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275558 p = 1 := by simpa only [d275559, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48228 p hg
    simpa only [d275559, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48230 (p : Pattern) (guard : d275560 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d275559 p = 1 := by simpa only [d275560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48229 p hg
    simpa only [d275560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48231 (p : Pattern) (guard : d275561 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d275560 p = 1 := by simpa only [d275561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48230 p hg
    simpa only [d275561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48232 (p : Pattern) (guard : d275562 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d275561 p = 1 := by simpa only [d275562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48231 p hg
    simpa only [d275562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48233 (p : Pattern) (guard : d275563 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d275562 p = 1 := by simpa only [d275563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48232 p hg
    simpa only [d275563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48234 (p : Pattern) (guard : d275564 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275563 p = 1 := by simpa only [d275564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48233 p hg
    simpa only [d275564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48235 (p : Pattern) (guard : d275866 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275564 p = 1 := by simpa only [d275866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48234 p hg
    simpa only [d275866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48236 (p : Pattern) (guard : d275867 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275866 p = 1 := by simpa only [d275867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48235 p hg
    simpa only [d275867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48237 (p : Pattern) (guard : d275868 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275867 p = 1 := by simpa only [d275868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48236 p hg
    simpa only [d275868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48238 (p : Pattern) (guard : d275869 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d275869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275868 p = 1 := by simpa only [d275869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48237 p hg
    simpa only [d275869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48239 (p : Pattern) (guard : d275870 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275870, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d275870, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275869 p = 1 := by simpa only [d275870, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48238 p hg
    simpa only [d275870, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48240 (p : Pattern) (guard : d275871 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d275871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275870 p = 1 := by simpa only [d275871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48239 p hg
    simpa only [d275871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48241 (p : Pattern) (guard : d277229 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d275871 p = 1 := by simpa only [d277229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48240 p hg
    simpa only [d277229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d277229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d277229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48242 (p : Pattern) (guard : d277230 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d277229 p = 1 := by simpa only [d277230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48241 p hg
    simpa only [d277230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d277230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d277230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48243 (p : Pattern) (guard : d277231 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d277230 p = 1 := by simpa only [d277231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48242 p hg
    simpa only [d277231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d277231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d277231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48244 (p : Pattern) (guard : d0 p = 1) : d50821 p ≤ (0 : Int) + d367983 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48245 (p : Pattern) (guard : d277232 p = 1) : d50822 p ≤ (0 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d277231 p = 1 := by simpa only [d277232, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48243 p hg
    simpa only [d277232, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d277232, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48244 p hg
    simpa only [d277232, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48246 (p : Pattern) (guard : d277233 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d277228 p = 1 := by simpa only [d277233, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48175 p hg
    simpa only [d277233, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277232 p = 1 := by simpa only [d277233, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48245 p hg
    simpa only [d277233, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48247 (p : Pattern) (guard : d277234 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d277234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d277234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277233 p = 1 := by simpa only [d277234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48246 p hg
    simpa only [d277234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48248 (p : Pattern) (guard : d277235 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d277235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d277235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277234 p = 1 := by simpa only [d277235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48247 p hg
    simpa only [d277235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48249 (p : Pattern) (guard : d277236 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d277236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d277236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d277235 p = 1 := by simpa only [d277236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48248 p hg
    simpa only [d277236, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
