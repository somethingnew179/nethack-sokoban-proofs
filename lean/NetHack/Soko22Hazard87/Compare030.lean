import NetHack.Soko22Hazard87.Compare029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7500 (p : Pattern) (guard : d2067 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7499 p hg
    simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7501 (p : Pattern) (guard : d2068 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7500 p hg
    simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7502 (p : Pattern) (guard : d2069 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7488 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2068 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7501 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7503 (p : Pattern) (guard : d2070 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2057 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7489 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2069 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7504 (p : Pattern) (guard : d2150 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2149 p = 1 := by simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7490 p hg
    simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2070 p = 1 := by simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7503 p hg
    simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7505 (p : Pattern) (guard : d2151 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2151, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d2151, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2150 p = 1 := by simpa only [d2151, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7504 p hg
    simpa only [d2151, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7506 (p : Pattern) (guard : d2152 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2152, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d2152, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2151 p = 1 := by simpa only [d2152, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7505 p hg
    simpa only [d2152, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7507 (p : Pattern) (guard : d2071 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7501 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7508 (p : Pattern) (guard : d2072 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2069 p = 1 := by simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2071 p = 1 := by simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7507 p hg
    simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7509 (p : Pattern) (guard : d2073 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2070 p = 1 := by simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7503 p hg
    simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2072 p = 1 := by simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7508 p hg
    simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7510 (p : Pattern) (guard : d2074 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2074, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d2074, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2073 p = 1 := by simpa only [d2074, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7509 p hg
    simpa only [d2074, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7511 (p : Pattern) (guard : d2075 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2075, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d2075, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2074 p = 1 := by simpa only [d2075, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7510 p hg
    simpa only [d2075, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7512 (p : Pattern) (guard : d2153 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2152 p = 1 := by simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7506 p hg
    simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2075 p = 1 := by simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7511 p hg
    simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7513 (p : Pattern) (guard : d2076 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7492 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7514 (p : Pattern) (guard : d2077 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7513 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7515 (p : Pattern) (guard : d2078 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7514 p hg
    simpa only [d2078, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d2078, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7516 (p : Pattern) (guard : d2079 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7515 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7517 (p : Pattern) (guard : d2080 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7516 p hg
    simpa only [d2080, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2080, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7518 (p : Pattern) (guard : d2081 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2080 p = 1 := by simpa only [d2081, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7517 p hg
    simpa only [d2081, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2081, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2081, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7519 (p : Pattern) (guard : d2082 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2082, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d2082, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2081 p = 1 := by simpa only [d2082, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7518 p hg
    simpa only [d2082, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7520 (p : Pattern) (guard : d2083 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2082 p = 1 := by simpa only [d2083, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7519 p hg
    simpa only [d2083, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2083, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d2083, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7521 (p : Pattern) (guard : d2084 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2083 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7520 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7522 (p : Pattern) (guard : d2085 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7507 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2084 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7521 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7523 (p : Pattern) (guard : d2086 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2072 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7508 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2085 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7522 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7524 (p : Pattern) (guard : d2087 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2087, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d2087, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2086 p = 1 := by simpa only [d2087, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7523 p hg
    simpa only [d2087, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7525 (p : Pattern) (guard : d2088 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2088, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d2088, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2087 p = 1 := by simpa only [d2088, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7524 p hg
    simpa only [d2088, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7526 (p : Pattern) (guard : d2089 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2075 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7511 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2088 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7525 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7527 (p : Pattern) (guard : d2154 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2153 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7512 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2089 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7526 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7528 (p : Pattern) (guard : d2155 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2154 p = 1 := by simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7527 p hg
    simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7529 (p : Pattern) (guard : d2156 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2155 p = 1 := by simpa only [d2156, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7528 p hg
    simpa only [d2156, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2156, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d2156, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7530 (p : Pattern) (guard : d2157 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2157, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d2157, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2156 p = 1 := by simpa only [d2157, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7529 p hg
    simpa only [d2157, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7531 (p : Pattern) (guard : d7115 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2075 p = 1 := by simpa only [d7115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7511 p hg
    simpa only [d7115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d7115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7532 (p : Pattern) (guard : d5237 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2069 p = 1 := by simpa only [d5237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d5237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d5237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7533 (p : Pattern) (guard : d5238 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2046 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7478 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7534 (p : Pattern) (guard : d5239 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5238 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7533 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7535 (p : Pattern) (guard : d5240 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7456 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5239 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7534 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7536 (p : Pattern) (guard : d5241 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5240 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7535 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7481 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7537 (p : Pattern) (guard : d5242 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5241 p = 1 := by simpa only [d5242, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7536 p hg
    simpa only [d5242, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5242, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d5242, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7538 (p : Pattern) (guard : d5243 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5239 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7534 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7480 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7539 (p : Pattern) (guard : d5244 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5243 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7538 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7494 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7540 (p : Pattern) (guard : d5245 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5244 p = 1 := by simpa only [d5245, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7539 p hg
    simpa only [d5245, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5245, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d5245, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7541 (p : Pattern) (guard : d5246 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5242 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7537 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7540 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7542 (p : Pattern) (guard : d5247 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7541 p hg
    simpa only [d5247, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d5247, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7543 (p : Pattern) (guard : d5248 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7542 p hg
    simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7544 (p : Pattern) (guard : d5249 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7543 p hg
    simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7545 (p : Pattern) (guard : d5250 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7544 p hg
    simpa only [d5250, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d5250, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7546 (p : Pattern) (guard : d5251 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7545 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7547 (p : Pattern) (guard : d5252 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7546 p hg
    simpa only [d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7548 (p : Pattern) (guard : d5253 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d5237 p = 1 := by simpa only [d5253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7532 p hg
    simpa only [d5253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5252 p = 1 := by simpa only [d5253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7547 p hg
    simpa only [d5253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7549 (p : Pattern) (guard : d5254 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5254, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d5254, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5253 p = 1 := by simpa only [d5254, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7548 p hg
    simpa only [d5254, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7550 (p : Pattern) (guard : d5255 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5255, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d5255, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5254 p = 1 := by simpa only [d5255, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7549 p hg
    simpa only [d5255, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7551 (p : Pattern) (guard : d5256 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d5255 p = 1 := by simpa only [d5256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7550 p hg
    simpa only [d5256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d5256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7552 (p : Pattern) (guard : d7116 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d7115 p = 1 := by simpa only [d7116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7531 p hg
    simpa only [d7116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5256 p = 1 := by simpa only [d7116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7551 p hg
    simpa only [d7116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7553 (p : Pattern) (guard : d7117 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d7116 p = 1 := by simpa only [d7117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7552 p hg
    simpa only [d7117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d7117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7554 (p : Pattern) (guard : d7118 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d7117 p = 1 := by simpa only [d7118, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7553 p hg
    simpa only [d7118, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7118, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d7118, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7555 (p : Pattern) (guard : d7119 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d7119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7118 p = 1 := by simpa only [d7119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7554 p hg
    simpa only [d7119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7556 (p : Pattern) (guard : d7120 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2157 p = 1 := by simpa only [d7120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7530 p hg
    simpa only [d7120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7119 p = 1 := by simpa only [d7120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7555 p hg
    simpa only [d7120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7557 (p : Pattern) (guard : d7121 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7120 p = 1 := by simpa only [d7121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7556 p hg
    simpa only [d7121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d7121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7558 (p : Pattern) (guard : d7122 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7121 p = 1 := by simpa only [d7122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7557 p hg
    simpa only [d7122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d7122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7559 (p : Pattern) (guard : d7134 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7122 p = 1 := by simpa only [d7134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7558 p hg
    simpa only [d7134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d7134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7560 (p : Pattern) (guard : d5257 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2089 p = 1 := by simpa only [d5257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7526 p hg
    simpa only [d5257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5256 p = 1 := by simpa only [d5257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7551 p hg
    simpa only [d5257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7561 (p : Pattern) (guard : d5258 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d5257 p = 1 := by simpa only [d5258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7560 p hg
    simpa only [d5258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d5258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7562 (p : Pattern) (guard : d5259 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5258 p = 1 := by simpa only [d5259, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7561 p hg
    simpa only [d5259, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5259, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d5259, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7563 (p : Pattern) (guard : d5260 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5260, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d5260, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5259 p = 1 := by simpa only [d5260, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7562 p hg
    simpa only [d5260, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7564 (p : Pattern) (guard : d2090 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2088 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7525 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7565 (p : Pattern) (guard : d2095 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2090 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7564 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7566 (p : Pattern) (guard : d2096 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2095 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7565 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7567 (p : Pattern) (guard : d2097 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2096 p = 1 := by simpa only [d2097, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7566 p hg
    simpa only [d2097, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2097, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d2097, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7568 (p : Pattern) (guard : d2098 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2098, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d2098, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2097 p = 1 := by simpa only [d2098, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7567 p hg
    simpa only [d2098, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7569 (p : Pattern) (guard : d7124 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d5260 p = 1 := by simpa only [d7124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7563 p hg
    simpa only [d7124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2098 p = 1 := by simpa only [d7124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7568 p hg
    simpa only [d7124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7570 (p : Pattern) (guard : d7125 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7124 p = 1 := by simpa only [d7125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7569 p hg
    simpa only [d7125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d7125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7571 (p : Pattern) (guard : d7126 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7125 p = 1 := by simpa only [d7126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7570 p hg
    simpa only [d7126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d7126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7572 (p : Pattern) (guard : d7135 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7126 p = 1 := by simpa only [d7135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7571 p hg
    simpa only [d7135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d7135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7573 (p : Pattern) (guard : d7136 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7134 p = 1 := by simpa only [d7136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7559 p hg
    simpa only [d7136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7135 p = 1 := by simpa only [d7136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7572 p hg
    simpa only [d7136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7574 (p : Pattern) (guard : d82238 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d7136 p = 1 := by simpa only [d82238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7573 p hg
    simpa only [d82238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7575 (p : Pattern) (guard : d2091 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2089 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7526 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2090 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7564 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7576 (p : Pattern) (guard : d2092 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2091 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7575 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7577 (p : Pattern) (guard : d2093 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2092 p = 1 := by simpa only [d2093, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7576 p hg
    simpa only [d2093, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2093, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d2093, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7578 (p : Pattern) (guard : d2094 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2094, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d2094, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2093 p = 1 := by simpa only [d2094, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7577 p hg
    simpa only [d2094, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7579 (p : Pattern) (guard : d6547 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2094 p = 1 := by simpa only [d6547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7578 p hg
    simpa only [d6547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7580 (p : Pattern) (guard : d6548 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6547 p = 1 := by simpa only [d6548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7579 p hg
    simpa only [d6548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7581 (p : Pattern) (guard : d6549 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6548 p = 1 := by simpa only [d6549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7580 p hg
    simpa only [d6549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7582 (p : Pattern) (guard : d6559 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6549 p = 1 := by simpa only [d6559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7581 p hg
    simpa only [d6559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7583 (p : Pattern) (guard : d6613 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6559 p = 1 := by simpa only [d6613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7582 p hg
    simpa only [d6613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7584 (p : Pattern) (guard : d6614 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6613 p = 1 := by simpa only [d6614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7583 p hg
    simpa only [d6614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7585 (p : Pattern) (guard : d82239 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82238 p = 1 := by simpa only [d82239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7574 p hg
    simpa only [d82239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6614 p = 1 := by simpa only [d82239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7584 p hg
    simpa only [d82239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7586 (p : Pattern) (guard : d82247 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82239 p = 1 := by simpa only [d82247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7585 p hg
    simpa only [d82247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7587 (p : Pattern) (guard : d82248 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82247 p = 1 := by simpa only [d82248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7586 p hg
    simpa only [d82248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7588 (p : Pattern) (guard : d82249 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82249, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82249, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82248 p = 1 := by simpa only [d82249, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7587 p hg
    simpa only [d82249, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7589 (p : Pattern) (guard : d82250 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82249 p = 1 := by simpa only [d82250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7588 p hg
    simpa only [d82250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7590 (p : Pattern) (guard : d2103 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2098 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7568 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7591 (p : Pattern) (guard : d2104 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2103 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7590 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7592 (p : Pattern) (guard : d2105 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2104 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7591 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7593 (p : Pattern) (guard : d2116 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2105 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7592 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7594 (p : Pattern) (guard : d2311 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2116 p = 1 := by simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7593 p hg
    simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7595 (p : Pattern) (guard : d2312 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2311 p = 1 := by simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7594 p hg
    simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7596 (p : Pattern) (guard : d2313 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2312 p = 1 := by simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7595 p hg
    simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7597 (p : Pattern) (guard : d2314 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2313 p = 1 := by simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7596 p hg
    simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7598 (p : Pattern) (guard : d2315 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2314 p = 1 := by simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7597 p hg
    simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7599 (p : Pattern) (guard : d2325 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2325, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2325, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2315 p = 1 := by simpa only [d2325, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7598 p hg
    simpa only [d2325, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7600 (p : Pattern) (guard : d2326 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2325 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7599 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7601 (p : Pattern) (guard : d82251 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82250 p = 1 := by simpa only [d82251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7589 p hg
    simpa only [d82251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2326 p = 1 := by simpa only [d82251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7600 p hg
    simpa only [d82251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7602 (p : Pattern) (guard : d82252 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82251 p = 1 := by simpa only [d82252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7601 p hg
    simpa only [d82252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7603 (p : Pattern) (guard : d82253 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82252 p = 1 := by simpa only [d82253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7602 p hg
    simpa only [d82253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7604 (p : Pattern) (guard : d82254 p = 1) : d47768 p ≤ (-1 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82246 p = 1 := by simpa only [d82254, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7422 p hg
    simpa only [d82254, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82253 p = 1 := by simpa only [d82254, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7603 p hg
    simpa only [d82254, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7605 (p : Pattern) (guard : d1997 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4521 p hg
    simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7606 (p : Pattern) (guard : d1998 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7605 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7607 (p : Pattern) (guard : d1999 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7606 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7608 (p : Pattern) (guard : d2000 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7607 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7609 (p : Pattern) (guard : d2001 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6886 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7610 (p : Pattern) (guard : d2002 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7609 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7611 (p : Pattern) (guard : d2003 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7610 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7612 (p : Pattern) (guard : d2004 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7608 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7611 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7613 (p : Pattern) (guard : d2005 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6886 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7614 (p : Pattern) (guard : d2006 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7613 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7615 (p : Pattern) (guard : d2007 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7614 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7616 (p : Pattern) (guard : d2008 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7615 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7617 (p : Pattern) (guard : d2009 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7612 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7616 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7618 (p : Pattern) (guard : d2010 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7617 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7619 (p : Pattern) (guard : d2011 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7618 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7620 (p : Pattern) (guard : d2012 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7619 p hg
    simpa only [d2012, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d2012, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7621 (p : Pattern) (guard : d2143 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2012 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7620 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7622 (p : Pattern) (guard : d2331 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2331, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d2331, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2143 p = 1 := by simpa only [d2331, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7621 p hg
    simpa only [d2331, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7623 (p : Pattern) (guard : d2144 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7315 p hg
    simpa only [d2144, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2144, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7624 (p : Pattern) (guard : d2332 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2331 p = 1 := by simpa only [d2332, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7622 p hg
    simpa only [d2332, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2144 p = 1 := by simpa only [d2332, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7623 p hg
    simpa only [d2332, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7625 (p : Pattern) (guard : d1997 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7626 (p : Pattern) (guard : d1998 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7625 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7627 (p : Pattern) (guard : d1999 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7626 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7628 (p : Pattern) (guard : d2000 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7627 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7629 (p : Pattern) (guard : d2001 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6915 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7630 (p : Pattern) (guard : d2002 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7629 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7631 (p : Pattern) (guard : d2003 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7630 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7632 (p : Pattern) (guard : d2004 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7628 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7631 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7633 (p : Pattern) (guard : d2005 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6915 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7634 (p : Pattern) (guard : d2006 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7633 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7635 (p : Pattern) (guard : d2007 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7634 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7636 (p : Pattern) (guard : d2008 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7635 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7637 (p : Pattern) (guard : d2009 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7632 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7636 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7638 (p : Pattern) (guard : d2010 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7637 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7639 (p : Pattern) (guard : d2011 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7638 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7640 (p : Pattern) (guard : d2012 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7639 p hg
    simpa only [d2012, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d2012, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7641 (p : Pattern) (guard : d2143 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2012 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7640 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7642 (p : Pattern) (guard : d2144 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7641 p hg
    simpa only [d2144, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2144, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7643 (p : Pattern) (guard : d2145 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2144 p = 1 := by simpa only [d2145, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7642 p hg
    simpa only [d2145, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2145, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2145, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7644 (p : Pattern) (guard : d2333 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2332 p = 1 := by simpa only [d2333, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7624 p hg
    simpa only [d2333, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2145 p = 1 := by simpa only [d2333, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7643 p hg
    simpa only [d2333, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7645 (p : Pattern) (guard : d2334 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2333 p = 1 := by simpa only [d2334, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7644 p hg
    simpa only [d2334, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2334, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d2334, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7646 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7605 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7647 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7606 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7646 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7648 (p : Pattern) (guard : d2015 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7607 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7647 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7649 (p : Pattern) (guard : d2016 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4720 p hg
    simpa only [d2016, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4521 p hg
    simpa only [d2016, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7650 (p : Pattern) (guard : d2017 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7605 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7649 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7651 (p : Pattern) (guard : d2018 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7650 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7652 (p : Pattern) (guard : d2019 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7610 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7651 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7653 (p : Pattern) (guard : d2020 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7648 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7652 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7654 (p : Pattern) (guard : d2021 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7649 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7655 (p : Pattern) (guard : d2022 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7654 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7656 (p : Pattern) (guard : d2023 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7614 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7655 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7657 (p : Pattern) (guard : d2024 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7656 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7658 (p : Pattern) (guard : d2025 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7653 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7657 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7659 (p : Pattern) (guard : d2026 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7617 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7658 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7660 (p : Pattern) (guard : d2027 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7646 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7661 (p : Pattern) (guard : d2028 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7662 (p : Pattern) (guard : d2029 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7661 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7663 (p : Pattern) (guard : d2030 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7662 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7664 (p : Pattern) (guard : d2031 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7663 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7665 (p : Pattern) (guard : d2032 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7659 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7664 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7666 (p : Pattern) (guard : d2033 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7665 p hg
    simpa only [d2033, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d2033, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7667 (p : Pattern) (guard : d2034 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7620 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7666 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7668 (p : Pattern) (guard : d2335 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2335, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d2335, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2034 p = 1 := by simpa only [d2335, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7667 p hg
    simpa only [d2335, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7669 (p : Pattern) (guard : d2035 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7206 p hg
    simpa only [d2035, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2035, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7670 (p : Pattern) (guard : d2336 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2335 p = 1 := by simpa only [d2336, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7668 p hg
    simpa only [d2336, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2035 p = 1 := by simpa only [d2336, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7669 p hg
    simpa only [d2336, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7671 (p : Pattern) (guard : d2013 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7625 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7672 (p : Pattern) (guard : d2014 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7626 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7671 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7673 (p : Pattern) (guard : d2015 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7627 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7672 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7674 (p : Pattern) (guard : d2016 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4736 p hg
    simpa only [d2016, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d2016, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7675 (p : Pattern) (guard : d2017 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7625 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7674 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7676 (p : Pattern) (guard : d2018 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7675 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7677 (p : Pattern) (guard : d2019 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7630 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7676 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7678 (p : Pattern) (guard : d2020 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7673 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7677 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7679 (p : Pattern) (guard : d2021 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7674 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7680 (p : Pattern) (guard : d2022 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7679 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7681 (p : Pattern) (guard : d2023 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7634 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7680 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7682 (p : Pattern) (guard : d2024 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7681 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7683 (p : Pattern) (guard : d2025 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7678 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7682 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7684 (p : Pattern) (guard : d2026 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7637 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7683 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7685 (p : Pattern) (guard : d2027 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7671 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7686 (p : Pattern) (guard : d2028 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7685 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7687 (p : Pattern) (guard : d2029 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7686 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7688 (p : Pattern) (guard : d2030 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7687 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7689 (p : Pattern) (guard : d2031 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7688 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7690 (p : Pattern) (guard : d2032 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7684 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7689 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7691 (p : Pattern) (guard : d2033 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7690 p hg
    simpa only [d2033, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d2033, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7692 (p : Pattern) (guard : d2034 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7640 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7691 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7693 (p : Pattern) (guard : d2035 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7692 p hg
    simpa only [d2035, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2035, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7694 (p : Pattern) (guard : d2036 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d2036, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2036, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7695 (p : Pattern) (guard : d2337 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2336 p = 1 := by simpa only [d2337, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7670 p hg
    simpa only [d2337, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2337, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7694 p hg
    simpa only [d2337, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7696 (p : Pattern) (guard : d2338 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2337 p = 1 := by simpa only [d2338, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7695 p hg
    simpa only [d2338, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2338, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d2338, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7697 (p : Pattern) (guard : d2339 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2334 p = 1 := by simpa only [d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7645 p hg
    simpa only [d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2338 p = 1 := by simpa only [d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7698 (p : Pattern) (guard : d2039 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7647 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7699 (p : Pattern) (guard : d2040 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7651 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7700 (p : Pattern) (guard : d2041 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7698 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7699 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7701 (p : Pattern) (guard : d2042 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7655 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7702 (p : Pattern) (guard : d2043 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7701 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7703 (p : Pattern) (guard : d2044 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7700 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7702 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7704 (p : Pattern) (guard : d2045 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7658 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7703 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7705 (p : Pattern) (guard : d2046 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7706 (p : Pattern) (guard : d2047 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7705 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7707 (p : Pattern) (guard : d2048 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7706 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7708 (p : Pattern) (guard : d2049 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7663 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7707 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7709 (p : Pattern) (guard : d2050 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7708 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7710 (p : Pattern) (guard : d2051 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7709 p hg
    simpa only [d2051, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d2051, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7711 (p : Pattern) (guard : d2052 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7666 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7710 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7712 (p : Pattern) (guard : d2340 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2340, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d2340, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2052 p = 1 := by simpa only [d2340, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d2340, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7713 (p : Pattern) (guard : d2053 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7224 p hg
    simpa only [d2053, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2053, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7714 (p : Pattern) (guard : d2341 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2340 p = 1 := by simpa only [d2341, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7712 p hg
    simpa only [d2341, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2053 p = 1 := by simpa only [d2341, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7713 p hg
    simpa only [d2341, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7715 (p : Pattern) (guard : d2039 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7672 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7685 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7716 (p : Pattern) (guard : d2040 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7676 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7717 (p : Pattern) (guard : d2041 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7715 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7716 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7718 (p : Pattern) (guard : d2042 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7680 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7719 (p : Pattern) (guard : d2043 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7718 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7720 (p : Pattern) (guard : d2044 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7717 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7719 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7721 (p : Pattern) (guard : d2045 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7683 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7720 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7722 (p : Pattern) (guard : d2046 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7685 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7723 (p : Pattern) (guard : d2047 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7724 (p : Pattern) (guard : d2048 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7723 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7725 (p : Pattern) (guard : d2049 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7688 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7724 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7726 (p : Pattern) (guard : d2050 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7721 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7725 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7727 (p : Pattern) (guard : d2051 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d2051, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d2051, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7728 (p : Pattern) (guard : d2052 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7691 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7727 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7729 (p : Pattern) (guard : d2053 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7728 p hg
    simpa only [d2053, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2053, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7730 (p : Pattern) (guard : d2054 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7729 p hg
    simpa only [d2054, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2054, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7731 (p : Pattern) (guard : d2342 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2341 p = 1 := by simpa only [d2342, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7714 p hg
    simpa only [d2342, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2342, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7730 p hg
    simpa only [d2342, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7732 (p : Pattern) (guard : d2343 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2342 p = 1 := by simpa only [d2343, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7731 p hg
    simpa only [d2343, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2343, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d2343, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7733 (p : Pattern) (guard : d2344 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2338 p = 1 := by simpa only [d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2343 p = 1 := by simpa only [d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7732 p hg
    simpa only [d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7734 (p : Pattern) (guard : d2345 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2339 p = 1 := by simpa only [d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7697 p hg
    simpa only [d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2344 p = 1 := by simpa only [d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7733 p hg
    simpa only [d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7735 (p : Pattern) (guard : d2058 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7699 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7736 (p : Pattern) (guard : d2059 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7735 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7702 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7737 (p : Pattern) (guard : d2060 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7736 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7707 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7738 (p : Pattern) (guard : d2061 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7707 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7739 (p : Pattern) (guard : d2062 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7737 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7740 (p : Pattern) (guard : d2063 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7739 p hg
    simpa only [d2063, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d2063, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7741 (p : Pattern) (guard : d2064 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7710 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7740 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7742 (p : Pattern) (guard : d2346 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2346, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d2346, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2064 p = 1 := by simpa only [d2346, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7741 p hg
    simpa only [d2346, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7743 (p : Pattern) (guard : d2065 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7236 p hg
    simpa only [d2065, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2065, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7744 (p : Pattern) (guard : d2347 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2346 p = 1 := by simpa only [d2347, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7742 p hg
    simpa only [d2347, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2065 p = 1 := by simpa only [d2347, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7743 p hg
    simpa only [d2347, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7745 (p : Pattern) (guard : d2058 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7716 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7746 (p : Pattern) (guard : d2059 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7745 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7719 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7747 (p : Pattern) (guard : d2060 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7746 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7724 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7748 (p : Pattern) (guard : d2061 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7724 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7749 (p : Pattern) (guard : d2062 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7747 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7748 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
