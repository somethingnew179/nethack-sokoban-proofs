import NetHack.Soko22Hazard87.Compare085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21500 (p : Pattern) (guard : d17162 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21486 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21499 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21501 (p : Pattern) (guard : d17163 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d17163, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21500 p hg
    simpa only [d17163, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21502 (p : Pattern) (guard : d17164 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d17164, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21501 p hg
    simpa only [d17164, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21503 (p : Pattern) (guard : d5246 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21504 (p : Pattern) (guard : d5247 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21503 p hg
    simpa only [d5247, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d5247, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21505 (p : Pattern) (guard : d5248 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21504 p hg
    simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d5248, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21506 (p : Pattern) (guard : d5249 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21505 p hg
    simpa only [d5249, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21507 (p : Pattern) (guard : d5250 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21506 p hg
    simpa only [d5250, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d5250, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21508 (p : Pattern) (guard : d5251 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21507 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21509 (p : Pattern) (guard : d10411 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21510 (p : Pattern) (guard : d10412 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10411 p = 1 := by simpa only [d10412, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21509 p hg
    simpa only [d10412, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10412, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10412, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21511 (p : Pattern) (guard : d10414 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10412 p = 1 := by simpa only [d10414, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21510 p hg
    simpa only [d10414, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10414, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10414, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21512 (p : Pattern) (guard : d15555 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15555, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d15555, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10414 p = 1 := by simpa only [d15555, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21511 p hg
    simpa only [d15555, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21513 (p : Pattern) (guard : d15556 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21512 p hg
    simpa only [d15556, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d15556, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21514 (p : Pattern) (guard : d15557 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21513 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21515 (p : Pattern) (guard : d15558 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21508 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21514 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21516 (p : Pattern) (guard : d17165 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21499 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21515 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21517 (p : Pattern) (guard : d17166 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d17166, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21516 p hg
    simpa only [d17166, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21518 (p : Pattern) (guard : d17167 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d17167, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21517 p hg
    simpa only [d17167, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21519 (p : Pattern) (guard : d17168 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21502 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21518 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21520 (p : Pattern) (guard : d2064 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21521 (p : Pattern) (guard : d2065 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21520 p hg
    simpa only [d2065, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d2065, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21522 (p : Pattern) (guard : d2066 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21521 p hg
    simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21523 (p : Pattern) (guard : d2067 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21522 p hg
    simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21524 (p : Pattern) (guard : d2068 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21523 p hg
    simpa only [d2068, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d2068, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21525 (p : Pattern) (guard : d2071 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21524 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21526 (p : Pattern) (guard : d15563 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21525 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21514 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21527 (p : Pattern) (guard : d17169 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21499 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21526 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21528 (p : Pattern) (guard : d17170 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d17170, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21527 p hg
    simpa only [d17170, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21529 (p : Pattern) (guard : d17171 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d17171, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21528 p hg
    simpa only [d17171, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21530 (p : Pattern) (guard : d17172 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21529 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21531 (p : Pattern) (guard : d17173 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21519 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21530 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21532 (p : Pattern) (guard : d17174 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21531 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21533 (p : Pattern) (guard : d17175 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21532 p hg
    simpa only [d17175, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d17175, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21534 (p : Pattern) (guard : d17176 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d17176, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21533 p hg
    simpa only [d17176, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21535 (p : Pattern) (guard : d17177 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21530 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21536 (p : Pattern) (guard : d17178 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21535 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21537 (p : Pattern) (guard : d17179 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21536 p hg
    simpa only [d17179, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d17179, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21538 (p : Pattern) (guard : d17180 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21537 p hg
    simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21539 (p : Pattern) (guard : d17181 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21534 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21538 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21540 (p : Pattern) (guard : d17182 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21539 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21541 (p : Pattern) (guard : d17183 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21540 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21542 (p : Pattern) (guard : d17197 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17183 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21541 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21543 (p : Pattern) (guard : d17185 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21538 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21544 (p : Pattern) (guard : d17186 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21543 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21545 (p : Pattern) (guard : d17187 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21544 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21546 (p : Pattern) (guard : d17198 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17187 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21545 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21547 (p : Pattern) (guard : d17199 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17197 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21542 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17198 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21546 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21548 (p : Pattern) (guard : d17200 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17199 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21547 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21549 (p : Pattern) (guard : d17201 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17200 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21548 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21550 (p : Pattern) (guard : d17202 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17201 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21549 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21551 (p : Pattern) (guard : d17203 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17202 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21550 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21552 (p : Pattern) (guard : d171208 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171208, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d171208, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17203 p = 1 := by simpa only [d171208, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21551 p hg
    simpa only [d171208, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21553 (p : Pattern) (guard : d171209 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171208 p = 1 := by simpa only [d171209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21552 p hg
    simpa only [d171209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21554 (p : Pattern) (guard : d171210 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171209 p = 1 := by simpa only [d171210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21553 p hg
    simpa only [d171210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21555 (p : Pattern) (guard : d171211 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171210 p = 1 := by simpa only [d171211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21554 p hg
    simpa only [d171211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21556 (p : Pattern) (guard : d171212 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171211 p = 1 := by simpa only [d171212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21555 p hg
    simpa only [d171212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21557 (p : Pattern) (guard : d171213 p = 1) : d48359 p ≤ (0 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171207 p = 1 := by simpa only [d171213, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21463 p hg
    simpa only [d171213, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171212 p = 1 := by simpa only [d171213, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21556 p hg
    simpa only [d171213, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21558 (p : Pattern) (guard : d175701 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171213 p = 1 := by simpa only [d175701, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21557 p hg
    simpa only [d175701, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175701, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20495 p hg
    simpa only [d175701, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21559 (p : Pattern) (guard : d175702 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175701 p = 1 := by simpa only [d175702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21558 p hg
    simpa only [d175702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21560 (p : Pattern) (guard : d175703 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175702 p = 1 := by simpa only [d175703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21559 p hg
    simpa only [d175703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21561 (p : Pattern) (guard : d175704 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175703 p = 1 := by simpa only [d175704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21560 p hg
    simpa only [d175704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21562 (p : Pattern) (guard : d175705 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175704 p = 1 := by simpa only [d175705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21561 p hg
    simpa only [d175705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21563 (p : Pattern) (guard : d175706 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175705 p = 1 := by simpa only [d175706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21562 p hg
    simpa only [d175706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21564 (p : Pattern) (guard : d175707 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175706 p = 1 := by simpa only [d175707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21563 p hg
    simpa only [d175707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21565 (p : Pattern) (guard : d175708 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175707 p = 1 := by simpa only [d175708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21564 p hg
    simpa only [d175708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21566 (p : Pattern) (guard : d175709 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175708 p = 1 := by simpa only [d175709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21565 p hg
    simpa only [d175709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21567 (p : Pattern) (guard : d175710 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175709 p = 1 := by simpa only [d175710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21566 p hg
    simpa only [d175710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21568 (p : Pattern) (guard : d175711 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175710 p = 1 := by simpa only [d175711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21567 p hg
    simpa only [d175711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21569 (p : Pattern) (guard : d175712 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d175700 p = 1 := by simpa only [d175712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21336 p hg
    simpa only [d175712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175711 p = 1 := by simpa only [d175712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21568 p hg
    simpa only [d175712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21570 (p : Pattern) (guard : d175713 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 260 with
  | false =>
    have hg : d175712 p = 1 := by simpa only [d175713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21569 p hg
    simpa only [d175713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21571 (p : Pattern) (guard : d175714 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 259 with
  | false =>
    have hg : d175713 p = 1 := by simpa only [d175714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21570 p hg
    simpa only [d175714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21572 (p : Pattern) (guard : d175715 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 258 with
  | false =>
    have hg : d175714 p = 1 := by simpa only [d175715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21571 p hg
    simpa only [d175715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21573 (p : Pattern) (guard : d175716 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 257 with
  | false =>
    have hg : d175715 p = 1 := by simpa only [d175716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21572 p hg
    simpa only [d175716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21574 (p : Pattern) (guard : d175717 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 256 with
  | false =>
    have hg : d175716 p = 1 := by simpa only [d175717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21573 p hg
    simpa only [d175717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21575 (p : Pattern) (guard : d175718 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 255 with
  | false =>
    have hg : d175717 p = 1 := by simpa only [d175718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21574 p hg
    simpa only [d175718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21576 (p : Pattern) (guard : d175719 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 254 with
  | false =>
    have hg : d175718 p = 1 := by simpa only [d175719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21575 p hg
    simpa only [d175719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21577 (p : Pattern) (guard : d175720 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 253 with
  | false =>
    have hg : d175719 p = 1 := by simpa only [d175720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21576 p hg
    simpa only [d175720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21578 (p : Pattern) (guard : d175721 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 252 with
  | false =>
    have hg : d175720 p = 1 := by simpa only [d175721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21577 p hg
    simpa only [d175721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21579 (p : Pattern) (guard : d175722 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 251 with
  | false =>
    have hg : d175721 p = 1 := by simpa only [d175722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21578 p hg
    simpa only [d175722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21580 (p : Pattern) (guard : d175723 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 250 with
  | false =>
    have hg : d175722 p = 1 := by simpa only [d175723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21579 p hg
    simpa only [d175723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21581 (p : Pattern) (guard : d175724 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 249 with
  | false =>
    have hg : d175723 p = 1 := by simpa only [d175724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21580 p hg
    simpa only [d175724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21582 (p : Pattern) (guard : d175725 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 245 with
  | false =>
    have hg : d175724 p = 1 := by simpa only [d175725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21581 p hg
    simpa only [d175725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21583 (p : Pattern) (guard : d175726 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 200 with
  | false =>
    have hg : d175725 p = 1 := by simpa only [d175726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21582 p hg
    simpa only [d175726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21584 (p : Pattern) (guard : d175727 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 199 with
  | false =>
    have hg : d175726 p = 1 := by simpa only [d175727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21583 p hg
    simpa only [d175727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21585 (p : Pattern) (guard : d175728 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 186 with
  | false =>
    have hg : d175727 p = 1 := by simpa only [d175728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21584 p hg
    simpa only [d175728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21586 (p : Pattern) (guard : d175729 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 185 with
  | false =>
    have hg : d175728 p = 1 := by simpa only [d175729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21585 p hg
    simpa only [d175729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21587 (p : Pattern) (guard : d175730 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 184 with
  | false =>
    have hg : d175729 p = 1 := by simpa only [d175730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21586 p hg
    simpa only [d175730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21588 (p : Pattern) (guard : d175731 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 181 with
  | false =>
    have hg : d175730 p = 1 := by simpa only [d175731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21587 p hg
    simpa only [d175731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21589 (p : Pattern) (guard : d175732 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 177 with
  | false =>
    have hg : d175731 p = 1 := by simpa only [d175732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21588 p hg
    simpa only [d175732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21590 (p : Pattern) (guard : d175733 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 164 with
  | false =>
    have hg : d175732 p = 1 := by simpa only [d175733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21589 p hg
    simpa only [d175733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21591 (p : Pattern) (guard : d175734 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 156 with
  | false =>
    have hg : d175733 p = 1 := by simpa only [d175734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21590 p hg
    simpa only [d175734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21592 (p : Pattern) (guard : d175735 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 155 with
  | false =>
    have hg : d175734 p = 1 := by simpa only [d175735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21591 p hg
    simpa only [d175735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21593 (p : Pattern) (guard : d175736 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 134 with
  | false =>
    have hg : d175735 p = 1 := by simpa only [d175736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21592 p hg
    simpa only [d175736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21594 (p : Pattern) (guard : d175737 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 133 with
  | false =>
    have hg : d175736 p = 1 := by simpa only [d175737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21593 p hg
    simpa only [d175737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21595 (p : Pattern) (guard : d175738 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 120 with
  | false =>
    have hg : d175737 p = 1 := by simpa only [d175738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21594 p hg
    simpa only [d175738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21596 (p : Pattern) (guard : d175739 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 118 with
  | false =>
    have hg : d175738 p = 1 := by simpa only [d175739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21595 p hg
    simpa only [d175739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21597 (p : Pattern) (guard : d175740 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 114 with
  | false =>
    have hg : d175739 p = 1 := by simpa only [d175740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21596 p hg
    simpa only [d175740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21598 (p : Pattern) (guard : d175741 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 111 with
  | false =>
    have hg : d175740 p = 1 := by simpa only [d175741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21597 p hg
    simpa only [d175741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21599 (p : Pattern) (guard : d175742 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 98 with
  | false =>
    have hg : d175741 p = 1 := by simpa only [d175742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21598 p hg
    simpa only [d175742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21600 (p : Pattern) (guard : d175743 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 97 with
  | false =>
    have hg : d175742 p = 1 := by simpa only [d175743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21599 p hg
    simpa only [d175743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21601 (p : Pattern) (guard : d175744 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 94 with
  | false =>
    have hg : d175743 p = 1 := by simpa only [d175744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21600 p hg
    simpa only [d175744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21602 (p : Pattern) (guard : d175745 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 76 with
  | false =>
    have hg : d175744 p = 1 := by simpa only [d175745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21601 p hg
    simpa only [d175745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21603 (p : Pattern) (guard : d175746 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 67 with
  | false =>
    have hg : d175745 p = 1 := by simpa only [d175746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21602 p hg
    simpa only [d175746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21604 (p : Pattern) (guard : d175747 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 52 with
  | false =>
    have hg : d175746 p = 1 := by simpa only [d175747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21603 p hg
    simpa only [d175747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21605 (p : Pattern) (guard : d175748 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 47 with
  | false =>
    have hg : d175747 p = 1 := by simpa only [d175748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21604 p hg
    simpa only [d175748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21606 (p : Pattern) (guard : d175749 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 46 with
  | false =>
    have hg : d175748 p = 1 := by simpa only [d175749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21605 p hg
    simpa only [d175749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21607 (p : Pattern) (guard : d175750 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 45 with
  | false =>
    have hg : d175749 p = 1 := by simpa only [d175750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21606 p hg
    simpa only [d175750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21608 (p : Pattern) (guard : d175751 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 30 with
  | false =>
    have hg : d175750 p = 1 := by simpa only [d175751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21607 p hg
    simpa only [d175751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21609 (p : Pattern) (guard : d175752 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 29 with
  | false =>
    have hg : d175751 p = 1 := by simpa only [d175752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21608 p hg
    simpa only [d175752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21610 (p : Pattern) (guard : d175753 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 28 with
  | false =>
    have hg : d175752 p = 1 := by simpa only [d175753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21609 p hg
    simpa only [d175753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21611 (p : Pattern) (guard : d175754 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 27 with
  | false =>
    have hg : d175753 p = 1 := by simpa only [d175754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21610 p hg
    simpa only [d175754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21612 (p : Pattern) (guard : d175755 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 25 with
  | false =>
    have hg : d175754 p = 1 := by simpa only [d175755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21611 p hg
    simpa only [d175755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21613 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21614 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21615 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21616 (p : Pattern) (guard : d0 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21617 (p : Pattern) (guard : d0 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21618 (p : Pattern) (guard : d0 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21619 (p : Pattern) (guard : d0 p = 1) : d48336 p ≤ (1 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21620 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (1 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21621 (p : Pattern) (guard : d0 p = 1) : d48325 p ≤ (1 : Int) + d47681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21622 (p : Pattern) (guard : d0 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21623 (p : Pattern) (guard : d29117 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare21624 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21625 (p : Pattern) (guard : d29118 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29117 p = 1 := by simpa only [d29118, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21623 p hg
    simpa only [d29118, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29118, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d29118, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21626 (p : Pattern) (guard : d179108 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29118 p = 1 := by simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21625 p hg
    simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21627 (p : Pattern) (guard : d179109 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179108 p = 1 := by simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21626 p hg
    simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21628 (p : Pattern) (guard : d179110 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179109 p = 1 := by simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21627 p hg
    simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21629 (p : Pattern) (guard : d179111 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179111, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179111, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179110 p = 1 := by simpa only [d179111, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21628 p hg
    simpa only [d179111, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21630 (p : Pattern) (guard : d179112 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179112, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179112, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179111 p = 1 := by simpa only [d179112, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21629 p hg
    simpa only [d179112, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21631 (p : Pattern) (guard : d0 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21632 (p : Pattern) (guard : d179113 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179112 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21630 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21633 (p : Pattern) (guard : d179114 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179113 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21632 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21634 (p : Pattern) (guard : d179115 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179114 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21633 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21635 (p : Pattern) (guard : d0 p = 1) : d48328 p ≤ (1 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21636 (p : Pattern) (guard : d179116 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179115 p = 1 := by simpa only [d179116, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21634 p hg
    simpa only [d179116, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179116, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179116, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21637 (p : Pattern) (guard : d179117 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179117, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179117, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179116 p = 1 := by simpa only [d179117, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21636 p hg
    simpa only [d179117, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21638 (p : Pattern) (guard : d179118 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179117 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21637 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21639 (p : Pattern) (guard : d179119 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179118 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21640 (p : Pattern) (guard : d179120 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179119 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21639 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21641 (p : Pattern) (guard : d179121 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179120 p = 1 := by simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21640 p hg
    simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21642 (p : Pattern) (guard : d179122 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179121 p = 1 := by simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21641 p hg
    simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21643 (p : Pattern) (guard : d179123 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179122 p = 1 := by simpa only [d179123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21642 p hg
    simpa only [d179123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21644 (p : Pattern) (guard : d179124 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179123 p = 1 := by simpa only [d179124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21643 p hg
    simpa only [d179124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21645 (p : Pattern) (guard : d179125 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179124 p = 1 := by simpa only [d179125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21644 p hg
    simpa only [d179125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21646 (p : Pattern) (guard : d179126 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179125 p = 1 := by simpa only [d179126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21645 p hg
    simpa only [d179126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21647 (p : Pattern) (guard : d179127 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179127, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179127, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179126 p = 1 := by simpa only [d179127, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21646 p hg
    simpa only [d179127, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21648 (p : Pattern) (guard : d0 p = 1) : d48321 p ≤ (1 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21649 (p : Pattern) (guard : d0 p = 1) : d48324 p ≤ (1 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21650 (p : Pattern) (guard : d179112 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179112, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179112, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179111 p = 1 := by simpa only [d179112, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21629 p hg
    simpa only [d179112, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21651 (p : Pattern) (guard : d0 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21652 (p : Pattern) (guard : d179113 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179112 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21650 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21653 (p : Pattern) (guard : d179114 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179113 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21652 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21654 (p : Pattern) (guard : d179115 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179114 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21653 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21655 (p : Pattern) (guard : d179116 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179115 p = 1 := by simpa only [d179116, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21654 p hg
    simpa only [d179116, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179116, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179116, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21656 (p : Pattern) (guard : d179117 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179117, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179117, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179116 p = 1 := by simpa only [d179117, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21655 p hg
    simpa only [d179117, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21657 (p : Pattern) (guard : d179118 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179117 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21656 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21658 (p : Pattern) (guard : d179119 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179118 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21657 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21659 (p : Pattern) (guard : d179120 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179119 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21658 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21660 (p : Pattern) (guard : d179121 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179120 p = 1 := by simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21659 p hg
    simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21661 (p : Pattern) (guard : d179122 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179121 p = 1 := by simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21660 p hg
    simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21662 (p : Pattern) (guard : d179123 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179122 p = 1 := by simpa only [d179123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21661 p hg
    simpa only [d179123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21663 (p : Pattern) (guard : d179124 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179123 p = 1 := by simpa only [d179124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21662 p hg
    simpa only [d179124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21664 (p : Pattern) (guard : d179125 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179124 p = 1 := by simpa only [d179125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21663 p hg
    simpa only [d179125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21665 (p : Pattern) (guard : d179126 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179125 p = 1 := by simpa only [d179126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21664 p hg
    simpa only [d179126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21666 (p : Pattern) (guard : d179128 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179120 p = 1 := by simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21640 p hg
    simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21667 (p : Pattern) (guard : d179129 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179128 p = 1 := by simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21666 p hg
    simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21668 (p : Pattern) (guard : d179130 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179129 p = 1 := by simpa only [d179130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21667 p hg
    simpa only [d179130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21669 (p : Pattern) (guard : d179131 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179130 p = 1 := by simpa only [d179131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21668 p hg
    simpa only [d179131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21670 (p : Pattern) (guard : d179132 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179131 p = 1 := by simpa only [d179132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21669 p hg
    simpa only [d179132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21671 (p : Pattern) (guard : d179133 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179132 p = 1 := by simpa only [d179133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21670 p hg
    simpa only [d179133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21672 (p : Pattern) (guard : d179134 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179126 p = 1 := by simpa only [d179134, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21665 p hg
    simpa only [d179134, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179133 p = 1 := by simpa only [d179134, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21671 p hg
    simpa only [d179134, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21673 (p : Pattern) (guard : d179135 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179127 p = 1 := by simpa only [d179135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21647 p hg
    simpa only [d179135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179134 p = 1 := by simpa only [d179135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21672 p hg
    simpa only [d179135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21674 (p : Pattern) (guard : d179136 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179135 p = 1 := by simpa only [d179136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21673 p hg
    simpa only [d179136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21675 (p : Pattern) (guard : d179137 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179136 p = 1 := by simpa only [d179137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21674 p hg
    simpa only [d179137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21676 (p : Pattern) (guard : d179138 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179137 p = 1 := by simpa only [d179138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21675 p hg
    simpa only [d179138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21677 (p : Pattern) (guard : d0 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21678 (p : Pattern) (guard : d0 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21679 (p : Pattern) (guard : d0 p = 1) : d48351 p ≤ (1 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21680 (p : Pattern) (guard : d0 p = 1) : d48353 p ≤ (1 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21681 (p : Pattern) (guard : d0 p = 1) : d48344 p ≤ (1 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21682 (p : Pattern) (guard : d0 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21683 (p : Pattern) (guard : d29117 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare21684 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21685 (p : Pattern) (guard : d29118 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29117 p = 1 := by simpa only [d29118, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21683 p hg
    simpa only [d29118, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29118, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d29118, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21686 (p : Pattern) (guard : d179108 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29118 p = 1 := by simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21685 p hg
    simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21687 (p : Pattern) (guard : d179109 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179108 p = 1 := by simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21686 p hg
    simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21688 (p : Pattern) (guard : d179110 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179109 p = 1 := by simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21687 p hg
    simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21689 (p : Pattern) (guard : d179111 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179111, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179111, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179110 p = 1 := by simpa only [d179111, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21688 p hg
    simpa only [d179111, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21690 (p : Pattern) (guard : d179112 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179112, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179112, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179111 p = 1 := by simpa only [d179112, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21689 p hg
    simpa only [d179112, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21691 (p : Pattern) (guard : d0 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21692 (p : Pattern) (guard : d179113 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179112 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21690 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21693 (p : Pattern) (guard : d179114 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179113 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21692 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21694 (p : Pattern) (guard : d179115 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179114 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21693 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21695 (p : Pattern) (guard : d0 p = 1) : d48355 p ≤ (1 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21696 (p : Pattern) (guard : d179116 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179115 p = 1 := by simpa only [d179116, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21694 p hg
    simpa only [d179116, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179116, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179116, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21697 (p : Pattern) (guard : d179117 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179117, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179117, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179116 p = 1 := by simpa only [d179117, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21696 p hg
    simpa only [d179117, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21698 (p : Pattern) (guard : d179118 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179117 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21697 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21699 (p : Pattern) (guard : d179119 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179118 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21698 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21700 (p : Pattern) (guard : d179120 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179119 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21699 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21701 (p : Pattern) (guard : d179128 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179120 p = 1 := by simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21700 p hg
    simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21702 (p : Pattern) (guard : d179129 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179128 p = 1 := by simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21701 p hg
    simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21703 (p : Pattern) (guard : d179130 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179129 p = 1 := by simpa only [d179130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21702 p hg
    simpa only [d179130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21704 (p : Pattern) (guard : d179131 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179130 p = 1 := by simpa only [d179131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21703 p hg
    simpa only [d179131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21705 (p : Pattern) (guard : d179132 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179131 p = 1 := by simpa only [d179132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21704 p hg
    simpa only [d179132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21706 (p : Pattern) (guard : d179133 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179132 p = 1 := by simpa only [d179133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21705 p hg
    simpa only [d179133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21707 (p : Pattern) (guard : d179139 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179139, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179139, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179133 p = 1 := by simpa only [d179139, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21706 p hg
    simpa only [d179139, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21708 (p : Pattern) (guard : d179140 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179139 p = 1 := by simpa only [d179140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21707 p hg
    simpa only [d179140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21709 (p : Pattern) (guard : d179141 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179140 p = 1 := by simpa only [d179141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21708 p hg
    simpa only [d179141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21710 (p : Pattern) (guard : d179142 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179141 p = 1 := by simpa only [d179142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21709 p hg
    simpa only [d179142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21711 (p : Pattern) (guard : d179143 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179142 p = 1 := by simpa only [d179143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21710 p hg
    simpa only [d179143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21712 (p : Pattern) (guard : d179144 p = 1) : d48359 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179138 p = 1 := by simpa only [d179144, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21676 p hg
    simpa only [d179144, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179143 p = 1 := by simpa only [d179144, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21711 p hg
    simpa only [d179144, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21713 (p : Pattern) (guard : d0 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21714 (p : Pattern) (guard : d0 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21715 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (1 : Int) + d47786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21716 (p : Pattern) (guard : d0 p = 1) : d48360 p ≤ (1 : Int) + d47796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21717 (p : Pattern) (guard : d0 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21718 (p : Pattern) (guard : d29397 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare21719 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21720 (p : Pattern) (guard : d29398 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29397 p = 1 := by simpa only [d29398, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21718 p hg
    simpa only [d29398, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29398, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d29398, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21721 (p : Pattern) (guard : d179145 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29398 p = 1 := by simpa only [d179145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21720 p hg
    simpa only [d179145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21722 (p : Pattern) (guard : d179146 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179145 p = 1 := by simpa only [d179146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21721 p hg
    simpa only [d179146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21723 (p : Pattern) (guard : d179147 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179146 p = 1 := by simpa only [d179147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21722 p hg
    simpa only [d179147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21724 (p : Pattern) (guard : d179148 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179148, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179148, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179147 p = 1 := by simpa only [d179148, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21723 p hg
    simpa only [d179148, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21725 (p : Pattern) (guard : d179149 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179149, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179149, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179148 p = 1 := by simpa only [d179149, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21724 p hg
    simpa only [d179149, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21726 (p : Pattern) (guard : d0 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21727 (p : Pattern) (guard : d179150 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179149 p = 1 := by simpa only [d179150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21725 p hg
    simpa only [d179150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21728 (p : Pattern) (guard : d179151 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179150 p = 1 := by simpa only [d179151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21727 p hg
    simpa only [d179151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21729 (p : Pattern) (guard : d179152 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179151 p = 1 := by simpa only [d179152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21728 p hg
    simpa only [d179152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21730 (p : Pattern) (guard : d0 p = 1) : d48364 p ≤ (1 : Int) + d47806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21731 (p : Pattern) (guard : d179153 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179152 p = 1 := by simpa only [d179153, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21729 p hg
    simpa only [d179153, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179153, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179153, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21732 (p : Pattern) (guard : d179154 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179154, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179154, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179153 p = 1 := by simpa only [d179154, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21731 p hg
    simpa only [d179154, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21733 (p : Pattern) (guard : d179155 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179154 p = 1 := by simpa only [d179155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21732 p hg
    simpa only [d179155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21734 (p : Pattern) (guard : d179156 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179155 p = 1 := by simpa only [d179156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21733 p hg
    simpa only [d179156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21735 (p : Pattern) (guard : d179157 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179156 p = 1 := by simpa only [d179157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21734 p hg
    simpa only [d179157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21736 (p : Pattern) (guard : d179158 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179157 p = 1 := by simpa only [d179158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21735 p hg
    simpa only [d179158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21737 (p : Pattern) (guard : d179159 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179158 p = 1 := by simpa only [d179159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21736 p hg
    simpa only [d179159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21738 (p : Pattern) (guard : d179160 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179159 p = 1 := by simpa only [d179160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21737 p hg
    simpa only [d179160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21739 (p : Pattern) (guard : d179161 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179160 p = 1 := by simpa only [d179161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21738 p hg
    simpa only [d179161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21740 (p : Pattern) (guard : d179162 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179161 p = 1 := by simpa only [d179162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21739 p hg
    simpa only [d179162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21741 (p : Pattern) (guard : d179163 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179162 p = 1 := by simpa only [d179163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21740 p hg
    simpa only [d179163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21742 (p : Pattern) (guard : d179164 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179164, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179164, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179163 p = 1 := by simpa only [d179164, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21741 p hg
    simpa only [d179164, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21743 (p : Pattern) (guard : d179165 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179164 p = 1 := by simpa only [d179165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21742 p hg
    simpa only [d179165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21744 (p : Pattern) (guard : d179166 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179165 p = 1 := by simpa only [d179166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21743 p hg
    simpa only [d179166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21745 (p : Pattern) (guard : d179167 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179166 p = 1 := by simpa only [d179167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21744 p hg
    simpa only [d179167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21746 (p : Pattern) (guard : d179168 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179167 p = 1 := by simpa only [d179168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21745 p hg
    simpa only [d179168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21747 (p : Pattern) (guard : d0 p = 1) : d48386 p ≤ (1 : Int) + d47864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21748 (p : Pattern) (guard : d179169 p = 1) : d48387 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179168 p = 1 := by simpa only [d179169, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21746 p hg
    simpa only [d179169, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179169, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21747 p hg
    simpa only [d179169, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21749 (p : Pattern) (guard : d179170 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d179144 p = 1 := by simpa only [d179170, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21712 p hg
    simpa only [d179170, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179169 p = 1 := by simpa only [d179170, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21748 p hg
    simpa only [d179170, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
