import NetHack.Soko22Hazard87.Compare073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18500 (p : Pattern) (guard : d641 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d640 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18499 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18501 (p : Pattern) (guard : d642 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d641 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18500 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18502 (p : Pattern) (guard : d643 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d642 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18501 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18503 (p : Pattern) (guard : d644 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d637 p = 1 := by simpa only [d644, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18497 p hg
    simpa only [d644, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d643 p = 1 := by simpa only [d644, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18502 p hg
    simpa only [d644, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18504 (p : Pattern) (guard : d16144 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16143 p = 1 := by simpa only [d16144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18492 p hg
    simpa only [d16144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d644 p = 1 := by simpa only [d16144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18503 p hg
    simpa only [d16144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18505 (p : Pattern) (guard : d128241 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128240 p = 1 := by simpa only [d128241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18486 p hg
    simpa only [d128241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16144 p = 1 := by simpa only [d128241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18504 p hg
    simpa only [d128241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18506 (p : Pattern) (guard : d128242 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128241 p = 1 := by simpa only [d128242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18505 p hg
    simpa only [d128242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d128242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18507 (p : Pattern) (guard : d128243 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d16060 p = 1 := by simpa only [d128243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18362 p hg
    simpa only [d128243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128242 p = 1 := by simpa only [d128243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18506 p hg
    simpa only [d128243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18508 (p : Pattern) (guard : d542 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18509 (p : Pattern) (guard : d543 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18508 p hg
    simpa only [d543, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d543, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18510 (p : Pattern) (guard : d544 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18509 p hg
    simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18511 (p : Pattern) (guard : d545 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18510 p hg
    simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18512 (p : Pattern) (guard : d546 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18511 p hg
    simpa only [d546, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d546, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18513 (p : Pattern) (guard : d9457 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18514 (p : Pattern) (guard : d9458 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9457 p = 1 := by simpa only [d9458, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18513 p hg
    simpa only [d9458, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9458, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9458, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18515 (p : Pattern) (guard : d9460 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9458 p = 1 := by simpa only [d9460, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18514 p hg
    simpa only [d9460, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9460, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9460, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18516 (p : Pattern) (guard : d16073 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16073, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d16073, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9460 p = 1 := by simpa only [d16073, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18515 p hg
    simpa only [d16073, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18517 (p : Pattern) (guard : d16074 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18516 p hg
    simpa only [d16074, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d16074, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18518 (p : Pattern) (guard : d16075 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18512 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18517 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18519 (p : Pattern) (guard : d9467 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18520 (p : Pattern) (guard : d9468 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9467 p = 1 := by simpa only [d9468, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18519 p hg
    simpa only [d9468, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9468, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9468, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18521 (p : Pattern) (guard : d9470 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9468 p = 1 := by simpa only [d9470, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18520 p hg
    simpa only [d9470, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9470, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9470, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18522 (p : Pattern) (guard : d12748 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12748, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d12748, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9470 p = 1 := by simpa only [d12748, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18521 p hg
    simpa only [d12748, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18523 (p : Pattern) (guard : d12749 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18522 p hg
    simpa only [d12749, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d12749, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18524 (p : Pattern) (guard : d16076 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18523 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12494 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18260 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18525 (p : Pattern) (guard : d16077 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18518 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16076 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18524 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18526 (p : Pattern) (guard : d16078 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16077 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18525 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15966 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18262 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18527 (p : Pattern) (guard : d16079 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16079, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16079, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16078 p = 1 := by simpa only [d16079, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18526 p hg
    simpa only [d16079, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18528 (p : Pattern) (guard : d16080 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16080, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16080, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16079 p = 1 := by simpa only [d16080, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18527 p hg
    simpa only [d16080, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18529 (p : Pattern) (guard : d16081 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12495 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18261 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17950 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18530 (p : Pattern) (guard : d16082 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18262 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16081 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18529 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18531 (p : Pattern) (guard : d16083 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16083, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16083, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16082 p = 1 := by simpa only [d16083, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18530 p hg
    simpa only [d16083, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18532 (p : Pattern) (guard : d16084 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16084, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16084, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16083 p = 1 := by simpa only [d16084, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18531 p hg
    simpa only [d16084, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18533 (p : Pattern) (guard : d16085 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16080 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18528 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16084 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18532 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18534 (p : Pattern) (guard : d16086 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16085 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18533 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15970 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18266 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18535 (p : Pattern) (guard : d16087 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16086 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18534 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18536 (p : Pattern) (guard : d16088 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16087 p = 1 := by simpa only [d16088, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18535 p hg
    simpa only [d16088, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16088, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16088, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18537 (p : Pattern) (guard : d16089 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16089, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16089, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16088 p = 1 := by simpa only [d16089, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18536 p hg
    simpa only [d16089, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18538 (p : Pattern) (guard : d475 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18097 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18539 (p : Pattern) (guard : d16035 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18266 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18538 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18540 (p : Pattern) (guard : d16036 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18539 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18541 (p : Pattern) (guard : d16037 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18540 p hg
    simpa only [d16037, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16037, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18542 (p : Pattern) (guard : d16038 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18541 p hg
    simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18543 (p : Pattern) (guard : d16090 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16089 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18537 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16038 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18542 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18544 (p : Pattern) (guard : d16091 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16090 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18543 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18545 (p : Pattern) (guard : d16092 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16091 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18544 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18546 (p : Pattern) (guard : d16130 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16092 p = 1 := by simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18545 p hg
    simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18547 (p : Pattern) (guard : d480 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18538 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18548 (p : Pattern) (guard : d481 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18547 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18549 (p : Pattern) (guard : d482 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18548 p hg
    simpa only [d482, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d482, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18550 (p : Pattern) (guard : d483 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18549 p hg
    simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18551 (p : Pattern) (guard : d16039 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18542 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18550 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18552 (p : Pattern) (guard : d16040 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18551 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18553 (p : Pattern) (guard : d16041 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18552 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18554 (p : Pattern) (guard : d16051 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16041 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18553 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18555 (p : Pattern) (guard : d16131 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16130 p = 1 := by simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18546 p hg
    simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16051 p = 1 := by simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18554 p hg
    simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18556 (p : Pattern) (guard : d128235 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16131 p = 1 := by simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18555 p hg
    simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18557 (p : Pattern) (guard : d16111 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18542 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18558 (p : Pattern) (guard : d16112 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16111 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18557 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18559 (p : Pattern) (guard : d16113 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16112 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18558 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18560 (p : Pattern) (guard : d16135 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16113 p = 1 := by simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18559 p hg
    simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18561 (p : Pattern) (guard : d16136 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16135 p = 1 := by simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18560 p hg
    simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18562 (p : Pattern) (guard : d16137 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16136 p = 1 := by simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18561 p hg
    simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18563 (p : Pattern) (guard : d128236 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128235 p = 1 := by simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18556 p hg
    simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16137 p = 1 := by simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18562 p hg
    simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18564 (p : Pattern) (guard : d128244 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128236 p = 1 := by simpa only [d128244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18563 p hg
    simpa only [d128244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18565 (p : Pattern) (guard : d128245 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128244 p = 1 := by simpa only [d128245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18564 p hg
    simpa only [d128245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18566 (p : Pattern) (guard : d128246 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128246, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128246, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128245 p = 1 := by simpa only [d128246, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18565 p hg
    simpa only [d128246, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18567 (p : Pattern) (guard : d128247 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128246 p = 1 := by simpa only [d128247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18566 p hg
    simpa only [d128247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18568 (p : Pattern) (guard : d488 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18550 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18569 (p : Pattern) (guard : d489 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18568 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18570 (p : Pattern) (guard : d490 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18569 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18571 (p : Pattern) (guard : d501 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18570 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18572 (p : Pattern) (guard : d639 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d501 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18571 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18573 (p : Pattern) (guard : d640 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d639 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18572 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18574 (p : Pattern) (guard : d641 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d640 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18573 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18575 (p : Pattern) (guard : d642 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d641 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18574 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18576 (p : Pattern) (guard : d643 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d642 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18575 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18577 (p : Pattern) (guard : d653 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d653, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d653, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d643 p = 1 := by simpa only [d653, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18576 p hg
    simpa only [d653, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18578 (p : Pattern) (guard : d654 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d653 p = 1 := by simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18577 p hg
    simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18579 (p : Pattern) (guard : d128248 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128247 p = 1 := by simpa only [d128248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18567 p hg
    simpa only [d128248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d654 p = 1 := by simpa only [d128248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18578 p hg
    simpa only [d128248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18580 (p : Pattern) (guard : d128249 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128248 p = 1 := by simpa only [d128249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18579 p hg
    simpa only [d128249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18581 (p : Pattern) (guard : d128250 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128249 p = 1 := by simpa only [d128250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18580 p hg
    simpa only [d128250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18582 (p : Pattern) (guard : d128251 p = 1) : d48359 p ≤ (1 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128243 p = 1 := by simpa only [d128251, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18507 p hg
    simpa only [d128251, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128250 p = 1 := by simpa only [d128251, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18581 p hg
    simpa only [d128251, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18583 (p : Pattern) (guard : d175457 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128251 p = 1 := by simpa only [d175457, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18582 p hg
    simpa only [d175457, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175457, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d175457, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18584 (p : Pattern) (guard : d175458 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175457 p = 1 := by simpa only [d175458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18583 p hg
    simpa only [d175458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18585 (p : Pattern) (guard : d175459 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175458 p = 1 := by simpa only [d175459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18584 p hg
    simpa only [d175459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18586 (p : Pattern) (guard : d175460 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175459 p = 1 := by simpa only [d175460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18585 p hg
    simpa only [d175460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18587 (p : Pattern) (guard : d175461 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175460 p = 1 := by simpa only [d175461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18586 p hg
    simpa only [d175461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18588 (p : Pattern) (guard : d175462 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175461 p = 1 := by simpa only [d175462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18587 p hg
    simpa only [d175462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18589 (p : Pattern) (guard : d175463 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175462 p = 1 := by simpa only [d175463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18588 p hg
    simpa only [d175463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18590 (p : Pattern) (guard : d175464 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d175456 p = 1 := by simpa only [d175464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18304 p hg
    simpa only [d175464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175463 p = 1 := by simpa only [d175464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18589 p hg
    simpa only [d175464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18591 (p : Pattern) (guard : d750 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18592 (p : Pattern) (guard : d751 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18591 p hg
    simpa only [d751, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d751, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18593 (p : Pattern) (guard : d752 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18592 p hg
    simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18594 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d753, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18593 p hg
    simpa only [d753, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18595 (p : Pattern) (guard : d754 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18594 p hg
    simpa only [d754, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d754, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18596 (p : Pattern) (guard : d12750 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18395 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18595 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18597 (p : Pattern) (guard : d16227 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18390 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18596 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18598 (p : Pattern) (guard : d755 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18159 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18595 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18599 (p : Pattern) (guard : d757 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18595 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18600 (p : Pattern) (guard : d758 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18598 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18599 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18601 (p : Pattern) (guard : d16228 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18597 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18600 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18602 (p : Pattern) (guard : d16229 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16229, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18601 p hg
    simpa only [d16229, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18603 (p : Pattern) (guard : d16230 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16230, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18602 p hg
    simpa only [d16230, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18604 (p : Pattern) (guard : d762 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18599 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18605 (p : Pattern) (guard : d763 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18600 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18604 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18606 (p : Pattern) (guard : d764 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d764, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18605 p hg
    simpa only [d764, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18607 (p : Pattern) (guard : d765 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d765, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18606 p hg
    simpa only [d765, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18608 (p : Pattern) (guard : d16231 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18603 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18607 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18609 (p : Pattern) (guard : d767 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18607 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18610 (p : Pattern) (guard : d16232 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18608 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18609 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18611 (p : Pattern) (guard : d16233 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18610 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18612 (p : Pattern) (guard : d16234 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18611 p hg
    simpa only [d16234, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16234, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18613 (p : Pattern) (guard : d16235 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16235, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18612 p hg
    simpa only [d16235, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18614 (p : Pattern) (guard : d772 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18609 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18615 (p : Pattern) (guard : d773 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18614 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18616 (p : Pattern) (guard : d774 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18615 p hg
    simpa only [d774, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d774, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18617 (p : Pattern) (guard : d775 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d775, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18616 p hg
    simpa only [d775, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18618 (p : Pattern) (guard : d16236 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18613 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18617 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18619 (p : Pattern) (guard : d16237 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18618 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18620 (p : Pattern) (guard : d16238 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18619 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18621 (p : Pattern) (guard : d16239 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16238 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18620 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18622 (p : Pattern) (guard : d780 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18617 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18623 (p : Pattern) (guard : d781 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18622 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18624 (p : Pattern) (guard : d782 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18623 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18625 (p : Pattern) (guard : d783 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18624 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18626 (p : Pattern) (guard : d16240 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16239 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18621 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18625 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18627 (p : Pattern) (guard : d16241 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16240 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18626 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18628 (p : Pattern) (guard : d16242 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16241 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18627 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18629 (p : Pattern) (guard : d16243 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16242 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18628 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18630 (p : Pattern) (guard : d16244 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16243 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18629 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18631 (p : Pattern) (guard : d16245 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16244 p = 1 := by simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18630 p hg
    simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18632 (p : Pattern) (guard : d16246 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16245 p = 1 := by simpa only [d16246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18631 p hg
    simpa only [d16246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18633 (p : Pattern) (guard : d16247 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16246 p = 1 := by simpa only [d16247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18632 p hg
    simpa only [d16247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18634 (p : Pattern) (guard : d16230 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16230, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18602 p hg
    simpa only [d16230, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18635 (p : Pattern) (guard : d765 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d765, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18606 p hg
    simpa only [d765, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18636 (p : Pattern) (guard : d16231 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18634 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18635 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18637 (p : Pattern) (guard : d767 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18635 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18638 (p : Pattern) (guard : d16232 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18637 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18639 (p : Pattern) (guard : d16233 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18638 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18640 (p : Pattern) (guard : d16234 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18639 p hg
    simpa only [d16234, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16234, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18641 (p : Pattern) (guard : d16235 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16235, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18640 p hg
    simpa only [d16235, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18642 (p : Pattern) (guard : d772 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18637 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18643 (p : Pattern) (guard : d773 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18642 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18644 (p : Pattern) (guard : d774 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18643 p hg
    simpa only [d774, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d774, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18645 (p : Pattern) (guard : d775 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d775, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18644 p hg
    simpa only [d775, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18646 (p : Pattern) (guard : d16236 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18641 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18645 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18647 (p : Pattern) (guard : d16237 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18646 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18648 (p : Pattern) (guard : d16238 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18647 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18649 (p : Pattern) (guard : d16239 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16238 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18648 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18650 (p : Pattern) (guard : d780 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18645 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18651 (p : Pattern) (guard : d781 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18650 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18652 (p : Pattern) (guard : d782 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18651 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18653 (p : Pattern) (guard : d783 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18652 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18654 (p : Pattern) (guard : d16240 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16239 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18649 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18653 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18655 (p : Pattern) (guard : d16241 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16240 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18654 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18656 (p : Pattern) (guard : d16242 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16241 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18655 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18657 (p : Pattern) (guard : d16243 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16242 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18656 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18658 (p : Pattern) (guard : d16244 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16243 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18657 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18659 (p : Pattern) (guard : d16248 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16238 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18620 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18660 (p : Pattern) (guard : d793 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18624 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18661 (p : Pattern) (guard : d16249 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16248 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18659 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18660 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18662 (p : Pattern) (guard : d16250 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16249 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18661 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18663 (p : Pattern) (guard : d16251 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16250 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18662 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18664 (p : Pattern) (guard : d16252 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16251 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18663 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18665 (p : Pattern) (guard : d16253 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16252 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18664 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18666 (p : Pattern) (guard : d16254 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16244 p = 1 := by simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18658 p hg
    simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16253 p = 1 := by simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18665 p hg
    simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18667 (p : Pattern) (guard : d16255 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16245 p = 1 := by simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18631 p hg
    simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16254 p = 1 := by simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18666 p hg
    simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18668 (p : Pattern) (guard : d16256 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16255 p = 1 := by simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18667 p hg
    simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18669 (p : Pattern) (guard : d16257 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16247 p = 1 := by simpa only [d16257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18633 p hg
    simpa only [d16257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16256 p = 1 := by simpa only [d16257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18668 p hg
    simpa only [d16257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18670 (p : Pattern) (guard : d16258 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16237 p = 1 := by simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18619 p hg
    simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18671 (p : Pattern) (guard : d16259 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16258 p = 1 := by simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18670 p hg
    simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18672 (p : Pattern) (guard : d805 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d781 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18623 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18673 (p : Pattern) (guard : d806 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d805 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18672 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18674 (p : Pattern) (guard : d16260 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16259 p = 1 := by simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18671 p hg
    simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d806 p = 1 := by simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18673 p hg
    simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18675 (p : Pattern) (guard : d16261 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16260 p = 1 := by simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18674 p hg
    simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18676 (p : Pattern) (guard : d16262 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16261 p = 1 := by simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18675 p hg
    simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18677 (p : Pattern) (guard : d16263 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16262 p = 1 := by simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18676 p hg
    simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18678 (p : Pattern) (guard : d16264 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16236 p = 1 := by simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18618 p hg
    simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18679 (p : Pattern) (guard : d16265 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16264 p = 1 := by simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18678 p hg
    simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18680 (p : Pattern) (guard : d16266 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16265 p = 1 := by simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18679 p hg
    simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18681 (p : Pattern) (guard : d814 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d780 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18622 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18682 (p : Pattern) (guard : d815 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d814 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18681 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18683 (p : Pattern) (guard : d816 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d815 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18682 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18684 (p : Pattern) (guard : d16267 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16266 p = 1 := by simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18680 p hg
    simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d816 p = 1 := by simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18683 p hg
    simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18685 (p : Pattern) (guard : d16268 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16267 p = 1 := by simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18684 p hg
    simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18686 (p : Pattern) (guard : d16269 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16268 p = 1 := by simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18685 p hg
    simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18687 (p : Pattern) (guard : d833 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18688 (p : Pattern) (guard : d834 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18687 p hg
    simpa only [d834, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d834, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18689 (p : Pattern) (guard : d835 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d834 p = 1 := by simpa only [d835, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18688 p hg
    simpa only [d835, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d835, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18690 (p : Pattern) (guard : d836 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d836, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18689 p hg
    simpa only [d836, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18691 (p : Pattern) (guard : d837 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18690 p hg
    simpa only [d837, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d837, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18692 (p : Pattern) (guard : d9586 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18693 (p : Pattern) (guard : d9587 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9586 p = 1 := by simpa only [d9587, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18692 p hg
    simpa only [d9587, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9587, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9587, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18694 (p : Pattern) (guard : d9589 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9587 p = 1 := by simpa only [d9589, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18693 p hg
    simpa only [d9589, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9589, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9589, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18695 (p : Pattern) (guard : d16270 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16270, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d16270, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9589 p = 1 := by simpa only [d16270, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18694 p hg
    simpa only [d16270, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18696 (p : Pattern) (guard : d16271 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16270 p = 1 := by simpa only [d16271, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18695 p hg
    simpa only [d16271, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16271, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d16271, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18697 (p : Pattern) (guard : d16272 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18691 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16271 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18696 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18698 (p : Pattern) (guard : d9596 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18699 (p : Pattern) (guard : d9597 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9596 p = 1 := by simpa only [d9597, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18698 p hg
    simpa only [d9597, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9597, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9597, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18700 (p : Pattern) (guard : d9599 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9597 p = 1 := by simpa only [d9599, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18699 p hg
    simpa only [d9599, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9599, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9599, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18701 (p : Pattern) (guard : d14529 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14529, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d14529, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9599 p = 1 := by simpa only [d14529, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18700 p hg
    simpa only [d14529, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18702 (p : Pattern) (guard : d14530 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14529 p = 1 := by simpa only [d14530, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18701 p hg
    simpa only [d14530, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14530, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d14530, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18703 (p : Pattern) (guard : d16273 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14530 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18702 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12749 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18395 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18704 (p : Pattern) (guard : d16274 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16272 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18697 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16273 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18703 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18705 (p : Pattern) (guard : d16275 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16274 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18704 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16227 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18597 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18706 (p : Pattern) (guard : d16276 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16276, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16276, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16275 p = 1 := by simpa only [d16276, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18705 p hg
    simpa only [d16276, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18707 (p : Pattern) (guard : d16277 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16277, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16277, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16276 p = 1 := by simpa only [d16277, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18706 p hg
    simpa only [d16277, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18708 (p : Pattern) (guard : d16278 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12750 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18596 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18599 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18709 (p : Pattern) (guard : d16279 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18597 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16278 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18708 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18710 (p : Pattern) (guard : d16280 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16280, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16280, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16279 p = 1 := by simpa only [d16280, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18709 p hg
    simpa only [d16280, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18711 (p : Pattern) (guard : d16281 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16281, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16281, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16280 p = 1 := by simpa only [d16281, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18710 p hg
    simpa only [d16281, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18712 (p : Pattern) (guard : d16282 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16277 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18707 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16281 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18711 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18713 (p : Pattern) (guard : d16283 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16282 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18712 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16231 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18608 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18714 (p : Pattern) (guard : d16284 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16283 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18713 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18715 (p : Pattern) (guard : d16285 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16284 p = 1 := by simpa only [d16285, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18714 p hg
    simpa only [d16285, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16285, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16285, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18716 (p : Pattern) (guard : d16286 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16286, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16286, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16285 p = 1 := by simpa only [d16286, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18715 p hg
    simpa only [d16286, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18717 (p : Pattern) (guard : d16287 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16286 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18716 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16235 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18613 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18718 (p : Pattern) (guard : d16288 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16287 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18717 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18719 (p : Pattern) (guard : d16289 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16288 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18718 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18720 (p : Pattern) (guard : d16290 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16289 p = 1 := by simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18719 p hg
    simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18721 (p : Pattern) (guard : d16291 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16290 p = 1 := by simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18720 p hg
    simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16239 p = 1 := by simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18621 p hg
    simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18722 (p : Pattern) (guard : d128270 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16291 p = 1 := by simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18721 p hg
    simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18723 (p : Pattern) (guard : d16311 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18613 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18724 (p : Pattern) (guard : d16312 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16311 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18723 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18725 (p : Pattern) (guard : d16313 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16312 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18724 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18726 (p : Pattern) (guard : d16314 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16313 p = 1 := by simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18725 p hg
    simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18727 (p : Pattern) (guard : d16315 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16314 p = 1 := by simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18726 p hg
    simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18728 (p : Pattern) (guard : d16316 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16315 p = 1 := by simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18727 p hg
    simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18729 (p : Pattern) (guard : d128271 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128270 p = 1 := by simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18722 p hg
    simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16316 p = 1 := by simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18728 p hg
    simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18730 (p : Pattern) (guard : d128272 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16269 p = 1 := by simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18686 p hg
    simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128271 p = 1 := by simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18729 p hg
    simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18731 (p : Pattern) (guard : d128273 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16263 p = 1 := by simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18677 p hg
    simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128272 p = 1 := by simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18730 p hg
    simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18732 (p : Pattern) (guard : d128274 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128274, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128274, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128273 p = 1 := by simpa only [d128274, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18731 p hg
    simpa only [d128274, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18733 (p : Pattern) (guard : d16258 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16237 p = 1 := by simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18647 p hg
    simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18734 (p : Pattern) (guard : d16259 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16258 p = 1 := by simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18733 p hg
    simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18735 (p : Pattern) (guard : d805 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d781 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18651 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18736 (p : Pattern) (guard : d806 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d805 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18735 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18737 (p : Pattern) (guard : d16260 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16259 p = 1 := by simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18734 p hg
    simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d806 p = 1 := by simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18736 p hg
    simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18738 (p : Pattern) (guard : d16261 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16260 p = 1 := by simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18737 p hg
    simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18739 (p : Pattern) (guard : d16262 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16261 p = 1 := by simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18738 p hg
    simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18740 (p : Pattern) (guard : d16263 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16262 p = 1 := by simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18739 p hg
    simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18741 (p : Pattern) (guard : d16264 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16236 p = 1 := by simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18646 p hg
    simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18742 (p : Pattern) (guard : d16265 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16264 p = 1 := by simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18741 p hg
    simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18743 (p : Pattern) (guard : d16266 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16265 p = 1 := by simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18742 p hg
    simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18744 (p : Pattern) (guard : d814 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d780 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18650 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18745 (p : Pattern) (guard : d815 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d814 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18744 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18746 (p : Pattern) (guard : d816 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d815 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18745 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18747 (p : Pattern) (guard : d16267 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16266 p = 1 := by simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18743 p hg
    simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d816 p = 1 := by simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18746 p hg
    simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18748 (p : Pattern) (guard : d16268 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16267 p = 1 := by simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18747 p hg
    simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18749 (p : Pattern) (guard : d16269 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16268 p = 1 := by simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18748 p hg
    simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
