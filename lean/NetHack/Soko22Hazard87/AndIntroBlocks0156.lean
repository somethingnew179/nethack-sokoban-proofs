import NetHack.Soko22Hazard87.AndIntroBlocks0155
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro39000 (p : Pattern) (ha : d18473 p = 1) (hb : d129250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18468 q = 1) (hb : d129245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18468, d129245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38999 q ha hb
    | true =>
      simp only [d18468, d129245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18469 q = 1) (hb : d129246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18469, d129246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18469, d129246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18470 q = 1) (hb : d129247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18470, d129247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18470, d129247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18471 q = 1) (hb : d129248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18471, d129248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18471, d129248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18472 q = 1) (hb : d129249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18472, d129249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18472, d129249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18473 q = 1) (hb : d129250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18473, d129250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18473, d129250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39001 (p : Pattern) (ha : d18317 p = 1) (hb : d129142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18309 q = 1) (hb : d129134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18309, d129134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18309, d129134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18310 q = 1) (hb : d129135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18310, d129135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18310, d129135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h7 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17370 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18311 q = 1) (hb : d129136 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18311, d129136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18311, d129136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18312 q = 1) (hb : d129137 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18312, d129137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18312, d129137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18313 q = 1) (hb : d129138 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18313, d129138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18313, d129138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h13 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18314 q = 1) (hb : d129139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d129139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18314, d129139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d18315 q = 1) (hb : d129140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d129140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18315, d129140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d18316 q = 1) (hb : d129141 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18316, d129141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18316, d129141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d18317 q = 1) (hb : d129142 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18317, d129142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18317, d129142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro39002 (p : Pattern) (ha : d18326 p = 1) (hb : d129151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2336 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18318 q = 1) (hb : d129143 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18318, d129143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18318, d129143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18319 q = 1) (hb : d129144 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18319, d129144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18319, d129144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h7 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17377 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18320 q = 1) (hb : d129145 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18320, d129145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18320, d129145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18321 q = 1) (hb : d129146 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18321, d129146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18321, d129146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18322 q = 1) (hb : d129147 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18322, d129147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18322, d129147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h13 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18314 q = 1) (hb : d129139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d129139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18314, d129139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d18315 q = 1) (hb : d129140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d129140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18315, d129140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h18 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d15776 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d18323 q = 1) (hb : d129148 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d129148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18323, d129148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d18324 q = 1) (hb : d129149 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d129149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18324, d129149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d18325 q = 1) (hb : d129150 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d129150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18325, d129150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d18326 q = 1) (hb : d129151 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18326, d129151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18326, d129151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39003 (p : Pattern) (ha : d18331 p = 1) (hb : d129156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18314 q = 1) (hb : d129139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d129139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18314, d129139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18315 q = 1) (hb : d129140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d129140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18315, d129140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h7 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15776 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18323 q = 1) (hb : d129148 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d129148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18323, d129148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18324 q = 1) (hb : d129149 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d129149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18324, d129149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18325 q = 1) (hb : d129150 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d129150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18325, d129150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18330 q = 1) (hb : d129155 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d129155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18330, d129155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18331 q = 1) (hb : d129156 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18331, d129156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18331, d129156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39004 (p : Pattern) (ha : d18351 p = 1) (hb : d129176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6644 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6644, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18345 q = 1) (hb : d129170 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18345, d129170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18345, d129170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18346 q = 1) (hb : d129171 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18346, d129171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18346, d129171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18347 q = 1) (hb : d129172 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18347, d129172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18347, d129172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h8 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18348 q = 1) (hb : d129173 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, d129173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18348, d129173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18349 q = 1) (hb : d129174 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d129174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18349, d129174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18350 q = 1) (hb : d129175 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d129175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18350, d129175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18351 q = 1) (hb : d129176 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18351, d129176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18351, d129176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39005 (p : Pattern) (ha : d18357 p = 1) (hb : d129182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18327 q = 1) (hb : d129152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18327, d129152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39001 q ha hb
    | true =>
      simp only [d18327, d129152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39002 q ha hb
  have h2 (q : Pattern) (ha : d18328 q = 1) (hb : d129153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18328, d129153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18328, d129153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18329 q = 1) (hb : d129154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18329, d129154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18329, d129154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18332 q = 1) (hb : d129157 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18332, d129157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39002 q ha hb
    | true =>
      simp only [d18332, d129157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39003 q ha hb
  have h5 (q : Pattern) (ha : d18333 q = 1) (hb : d129158 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18333, d129158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18333, d129158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18334 q = 1) (hb : d129159 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18334, d129159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18334, d129159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18335 q = 1) (hb : d129160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18335, d129160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18335, d129160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18342 q = 1) (hb : d129167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d129167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39002 q ha hb
    | true =>
      simp only [d18342, d129167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
  have h9 (q : Pattern) (ha : d18343 q = 1) (hb : d129168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d129168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d129168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18344 q = 1) (hb : d129169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d129169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d129169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18352 q = 1) (hb : d129177 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d129177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
    | true =>
      simp only [d18352, d129177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39004 q ha hb
  have h12 (q : Pattern) (ha : d18353 q = 1) (hb : d129178 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d129178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d129178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18354 q = 1) (hb : d129179 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d129179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d129179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18355 q = 1) (hb : d129180 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d129180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18355, d129180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18356 q = 1) (hb : d129181 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18356, d129181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18356, d129181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18357 q = 1) (hb : d129182 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18357, d129182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18357, d129182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39006 (p : Pattern) (ha : d18362 p = 1) (hb : d129187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d129167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d129167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39002 q ha hb
    | true =>
      simp only [d18342, d129167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d129168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d129168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d129168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d129169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d129169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d129169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d129177 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d129177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
    | true =>
      simp only [d18352, d129177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39004 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d129178 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d129178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d129178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d129179 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d129179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d129179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d129180 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d129180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d129180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18360 q = 1) (hb : d129185 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18360, d129185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18360, d129185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18361 q = 1) (hb : d129186 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18361, d129186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18361, d129186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18362 q = 1) (hb : d129187 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18362, d129187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18362, d129187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39007 (p : Pattern) (ha : d18368 p = 1) (hb : d129193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18358 q = 1) (hb : d129183 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18358, d129183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39005 q ha hb
    | true =>
      simp only [d18358, d129183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18359 q = 1) (hb : d129184 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18359, d129184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18359, d129184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18363 q = 1) (hb : d129188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, d129188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39006 q ha hb
    | true =>
      simp only [d18363, d129188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18364 q = 1) (hb : d129189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, d129189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, d129189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18365 q = 1) (hb : d129190 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18365, d129190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18365, d129190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18366 q = 1) (hb : d129191 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18366, d129191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18366, d129191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18367 q = 1) (hb : d129192 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18367, d129192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18367, d129192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18368 q = 1) (hb : d129193 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18368, d129193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18368, d129193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39008 (p : Pattern) (ha : d18384 p = 1) (hb : d129209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18363 q = 1) (hb : d129188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, d129188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39006 q ha hb
    | true =>
      simp only [d18363, d129188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18364 q = 1) (hb : d129189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, d129189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, d129189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d129204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d129204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38998 q ha hb
    | true =>
      simp only [d18379, d129204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d129205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d129205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d129205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18381 q = 1) (hb : d129206 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18381, d129206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18381, d129206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18382 q = 1) (hb : d129207 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18382, d129207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18382, d129207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18383 q = 1) (hb : d129208 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18383, d129208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18383, d129208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18384 q = 1) (hb : d129209 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18384, d129209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18384, d129209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39009 (p : Pattern) (ha : d18444 p = 1) (hb : d129225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18369 q = 1) (hb : d129194 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, d129194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18369, d129194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18370 q = 1) (hb : d129195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d129195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18370, d129195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18371 q = 1) (hb : d129196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d129196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18371, d129196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18444 q = 1) (hb : d129225 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18444, d129225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18444, d129225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39010 (p : Pattern) (ha : d18450 p = 1) (hb : d129231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d129167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d129167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39002 q ha hb
    | true =>
      simp only [d18342, d129167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d129168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d129168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d129168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d129169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d129169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d129169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d129177 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d129177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
    | true =>
      simp only [d18352, d129177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39004 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d129178 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d129178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d129178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d129179 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d129179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d129179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d129180 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d129180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d129180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18445 q = 1) (hb : d129226 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18445, d129226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
    | true =>
      simp only [d18445, d129226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39009 q ha hb
  have h9 (q : Pattern) (ha : d18446 q = 1) (hb : d129227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18446, d129227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18446, d129227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18447 q = 1) (hb : d129228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18447, d129228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18447, d129228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18448 q = 1) (hb : d129229 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18448, d129229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18448, d129229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18449 q = 1) (hb : d129230 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18449, d129230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18449, d129230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18450 q = 1) (hb : d129231 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18450, d129231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18450, d129231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39011 (p : Pattern) (ha : d18456 p = 1) (hb : d129237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18451 q = 1) (hb : d129232 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18451, d129232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39010 q ha hb
    | true =>
      simp only [d18451, d129232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18452 q = 1) (hb : d129233 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18452, d129233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18452, d129233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18453 q = 1) (hb : d129234 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18453, d129234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18453, d129234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18454 q = 1) (hb : d129235 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18454, d129235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18454, d129235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18455 q = 1) (hb : d129236 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18455, d129236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18455, d129236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18456 q = 1) (hb : d129237 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18456, d129237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18456, d129237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39012 (p : Pattern) (ha : d129243 p = 1) (hb : d129410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18385 q = 1) (hb : d129210 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18385, d129210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39007 q ha hb
    | true =>
      simp only [d18385, d129210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39008 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129224 q = 1) (hb : d129406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129224, d129406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129224, d129406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18457 q = 1) (hb : d129238 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18457, d129238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39011 q ha hb
    | true =>
      simp only [d18457, d129238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18458 q = 1) (hb : d129239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18458, d129239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18458, d129239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129240 q = 1) (hb : d129407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129240, d129407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129240, d129407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d129241 q = 1) (hb : d129408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129241, d129408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129241, d129408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129242 q = 1) (hb : d129409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129242, d129409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129242, d129409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129243 q = 1) (hb : d129410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129243, d129410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129243, d129410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39013 (p : Pattern) (ha : d129256 p = 1) (hb : d129416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129244 q = 1) (hb : d129411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129244, d129411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129244, d129411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39012 q ha hb
  have h2 (q : Pattern) (ha : d18474 q = 1) (hb : d129251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18474, d129251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18474, d129251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39000 q ha hb
  have h3 (q : Pattern) (ha : d129252 q = 1) (hb : d129412 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129252, d129412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129252, d129412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129253 q = 1) (hb : d129413 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129253, d129413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129253, d129413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129254 q = 1) (hb : d129414 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129254, d129414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129254, d129414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129255 q = 1) (hb : d129415 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129255, d129415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129255, d129415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129256 q = 1) (hb : d129416 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129256, d129416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129256, d129416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39014 (p : Pattern) (ha : d129262 p = 1) (hb : d129422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129257 q = 1) (hb : d129417 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129257, d129417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129257, d129417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39013 q ha hb
  have h2 (q : Pattern) (ha : d129258 q = 1) (hb : d129418 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129258, d129418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129258, d129418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129259 q = 1) (hb : d129419 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129259, d129419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129259, d129419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129260 q = 1) (hb : d129420 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129260, d129420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129260, d129420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129261 q = 1) (hb : d129421 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129261, d129421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129261, d129421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129262 q = 1) (hb : d129422 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129262, d129422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129262, d129422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39015 (p : Pattern) (ha : d129268 p = 1) (hb : d129428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128769 q = 1) (hb : d129345 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128769, d129345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38928 q ha hb
    | true =>
      simp only [d128769, d129345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38941 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128859 q = 1) (hb : d129363 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128859, d129363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128859, d129363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38957 q ha hb
  have h3 (q : Pattern) (ha : d128860 q = 1) (hb : d129364 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128860, d129364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128860, d129364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128993 q = 1) (hb : d129382 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128993, d129382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128993, d129382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38976 q ha hb
  have h5 (q : Pattern) (ha : d128994 q = 1) (hb : d129383 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128994, d129383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128994, d129383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128995 q = 1) (hb : d129384 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128995, d129384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128995, d129384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129130 q = 1) (hb : d129402 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129130, d129402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129130, d129402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38995 q ha hb
  have h8 (q : Pattern) (ha : d129131 q = 1) (hb : d129403 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129131, d129403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129131, d129403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129132 q = 1) (hb : d129404 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129132, d129404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129132, d129404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129133 q = 1) (hb : d129405 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129133, d129405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129133, d129405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129263 q = 1) (hb : d129423 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129263, d129423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129263, d129423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39014 q ha hb
  have h12 (q : Pattern) (ha : d129264 q = 1) (hb : d129424 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129264, d129424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129264, d129424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129265 q = 1) (hb : d129425 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129265, d129425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129265, d129425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129266 q = 1) (hb : d129426 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129266, d129426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129266, d129426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129267 q = 1) (hb : d129427 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129267, d129427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129267, d129427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129268 q = 1) (hb : d129428 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129268, d129428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129268, d129428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro39016 (p : Pattern) (ha : d129274 p = 1) (hb : d129434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129269 q = 1) (hb : d129429 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129269, d129429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39015 q ha hb
    | true =>
      simp only [d129269, d129429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129270 q = 1) (hb : d129430 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129270, d129430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129270, d129430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129271 q = 1) (hb : d129431 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129271, d129431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129271, d129431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129272 q = 1) (hb : d129432 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129272, d129432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129272, d129432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129273 q = 1) (hb : d129433 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129273, d129433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129273, d129433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129274 q = 1) (hb : d129434 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129274, d129434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129274, d129434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39017 (p : Pattern) (ha : d129280 p = 1) (hb : d129440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129275 q = 1) (hb : d129435 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129275, d129435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39016 q ha hb
    | true =>
      simp only [d129275, d129435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129276 q = 1) (hb : d129436 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129276, d129436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129276, d129436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129277 q = 1) (hb : d129437 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129277, d129437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129277, d129437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129278 q = 1) (hb : d129438 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129278, d129438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129278, d129438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129279 q = 1) (hb : d129439 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129279, d129439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129279, d129439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129280 q = 1) (hb : d129440 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129280, d129440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129280, d129440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39018 (p : Pattern) (ha : d129286 p = 1) (hb : d129446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129281 q = 1) (hb : d129441 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129281, d129441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39017 q ha hb
    | true =>
      simp only [d129281, d129441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129282 q = 1) (hb : d129442 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129282, d129442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129282, d129442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129283 q = 1) (hb : d129443 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129283, d129443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129283, d129443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129284 q = 1) (hb : d129444 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129284, d129444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129284, d129444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129285 q = 1) (hb : d129445 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129285, d129445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129285, d129445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129286 q = 1) (hb : d129446 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129286, d129446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129286, d129446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39019 (p : Pattern) (ha : d129292 p = 1) (hb : d129452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129287 q = 1) (hb : d129447 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129287, d129447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39018 q ha hb
    | true =>
      simp only [d129287, d129447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129288 q = 1) (hb : d129448 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129288, d129448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129288, d129448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129289 q = 1) (hb : d129449 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129289, d129449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129289, d129449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129290 q = 1) (hb : d129450 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129290, d129450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129290, d129450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129291 q = 1) (hb : d129451 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129291, d129451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129291, d129451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129292 q = 1) (hb : d129452 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129292, d129452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129292, d129452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39020 (p : Pattern) (ha : d129298 p = 1) (hb : d129458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129293 q = 1) (hb : d129453 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129293, d129453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39019 q ha hb
    | true =>
      simp only [d129293, d129453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129294 q = 1) (hb : d129454 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129294, d129454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129294, d129454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129295 q = 1) (hb : d129455 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129295, d129455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129295, d129455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129296 q = 1) (hb : d129456 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129296, d129456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129296, d129456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129297 q = 1) (hb : d129457 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129297, d129457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129297, d129457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129298 q = 1) (hb : d129458 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129298, d129458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129298, d129458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39021 (p : Pattern) (ha : d129304 p = 1) (hb : d129464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129299 q = 1) (hb : d129459 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129299, d129459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39020 q ha hb
    | true =>
      simp only [d129299, d129459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129300 q = 1) (hb : d129460 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129300, d129460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129300, d129460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129301 q = 1) (hb : d129461 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129301, d129461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129301, d129461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129302 q = 1) (hb : d129462 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129302, d129462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129302, d129462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129303 q = 1) (hb : d129463 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129303, d129463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129303, d129463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129304 q = 1) (hb : d129464 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129304, d129464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129304, d129464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39022 (p : Pattern) (ha : d129310 p = 1) (hb : d129470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129305 q = 1) (hb : d129465 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129305, d129465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39021 q ha hb
    | true =>
      simp only [d129305, d129465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129306 q = 1) (hb : d129466 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129306, d129466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129306, d129466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129307 q = 1) (hb : d129467 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129307, d129467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129307, d129467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129308 q = 1) (hb : d129468 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129308, d129468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129308, d129468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129309 q = 1) (hb : d129469 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129309, d129469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129309, d129469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129310 q = 1) (hb : d129470 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129310, d129470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129310, d129470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39023 (p : Pattern) (ha : d53647 p = 1) (hb : d128579 p = 1) : d61083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38598 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38599 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38620 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d128579 q = 1) : d17697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38621 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d128579 q = 1) : d61079 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d128579 q = 1) : d61080 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d128579 q = 1) : d61081 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d128579 q = 1) : d61082 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d128579 q = 1) : d61083 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39024 (p : Pattern) (ha : d53655 p = 1) (hb : d128579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38603 q ha hb
    | true =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38590 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39025 (p : Pattern) (ha : d53665 p = 1) (hb : d128579 p = 1) : d61093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d128579 q = 1) : d17609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38607 q ha hb
    | true =>
      simp only [d244, d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38595 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d128579 q = 1) : d61089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d61089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d61089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d128579 q = 1) : d61090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d61090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, d61090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d128579 q = 1) : d61091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d61091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d61091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d128579 q = 1) : d61092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d61092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d61092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d128579 q = 1) : d61093 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d61093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d61093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39026 (p : Pattern) (ha : d53671 p = 1) (hb : d128579 p = 1) : d61099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38617 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38618 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39024 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d128579 q = 1) : d61094 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d61094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d61094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39025 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d128579 q = 1) : d61095 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d61095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d61095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d128579 q = 1) : d61096 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d61096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d61096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d128579 q = 1) : d61097 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d61097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d61097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d128579 q = 1) : d61098 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d61098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d61098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d128579 q = 1) : d61099 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d61099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d61099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39027 (p : Pattern) (ha : d53677 p = 1) (hb : d128579 p = 1) : d61105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d128579 q = 1) : d61084 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39023 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d128579 q = 1) : d61085 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d128579 q = 1) : d61086 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d128579 q = 1) : d61087 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d128579 q = 1) : d61088 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d128579 q = 1) : d61100 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d61100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d61100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39026 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d128579 q = 1) : d61101 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d61101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d61101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d128579 q = 1) : d61102 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d61102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d61102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d128579 q = 1) : d61103 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d61103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d61103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d128579 q = 1) : d61104 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d61104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d61104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d128579 q = 1) : d61105 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d61105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d61105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39028 (p : Pattern) (ha : d128579 p = 1) (hb : d171078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38653 q ha hb
    | true =>
      simp only [d16052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38644 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171078 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro39029 (p : Pattern) (ha : d128579 p = 1) (hb : d171089 p = 1) : d173535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171084 q = 1) : d173530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38679 q hb ha
    | true =>
      simp only [d171084, d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38648 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171085 q = 1) : d173531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171085, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171086 q = 1) : d173532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171087 q = 1) : d173533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171087, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171088 q = 1) : d173534 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171088, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171089 q = 1) : d173535 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171089, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39030 (p : Pattern) (ha : d128579 p = 1) (hb : d171095 p = 1) : d173541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38652 q ha hb
    | true =>
      simp only [d16058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38654 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171076 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171077 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171079 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39028 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171080 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171081 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171082 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128579 q = 1) (hb : d171083 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128579 q = 1) (hb : d171090 q = 1) : d173536 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171090, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39029 q ha hb
  have h11 (q : Pattern) (ha : d128579 q = 1) (hb : d171091 q = 1) : d173537 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171092 q = 1) : d173538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171093 q = 1) : d173539 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d128579 q = 1) (hb : d171094 q = 1) : d173540 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d128579 q = 1) (hb : d171095 q = 1) : d173541 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39031 (p : Pattern) (ha : d128579 p = 1) (hb : d171101 p = 1) : d173547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171096 q = 1) : d173542 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171096, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39030 q ha hb
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171097 q = 1) : d173543 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171097, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171098 q = 1) : d173544 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171098, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171099 q = 1) : d173545 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171099, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171100 q = 1) : d173546 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171100, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171101 q = 1) : d173547 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171101, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39032 (p : Pattern) (ha : d128579 p = 1) (hb : d171105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16249 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38700 q ha hb
    | true =>
      simp only [d16249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38688 q ha hb
  have h2 (q : Pattern) (ha : d16250 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16251 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16252 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16253 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171105 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro39033 (p : Pattern) (ha : d128579 p = 1) (hb : d171116 p = 1) : d173554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171111 q = 1) : d173549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38727 q hb ha
    | true =>
      simp only [d171111, d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38694 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171112 q = 1) : d173550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171112, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171113 q = 1) : d173551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171114 q = 1) : d173552 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171114, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171115 q = 1) : d173553 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171115, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171116 q = 1) : d173554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171116, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39034 (p : Pattern) (ha : d128579 p = 1) (hb : d171122 p = 1) : d173560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16255 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38699 q ha hb
    | true =>
      simp only [d16255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38701 q ha hb
  have h2 (q : Pattern) (ha : d16256 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171103 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171104 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171106 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39032 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171107 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171108 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171109 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128579 q = 1) (hb : d171110 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128579 q = 1) (hb : d171117 q = 1) : d173555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171117, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39033 q ha hb
  have h11 (q : Pattern) (ha : d128579 q = 1) (hb : d171118 q = 1) : d173556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171118, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171119 q = 1) : d173557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171119, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171120 q = 1) : d173558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171120, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d128579 q = 1) (hb : d171121 q = 1) : d173559 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171121, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d128579 q = 1) (hb : d171122 q = 1) : d173560 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171122, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39035 (p : Pattern) (ha : d128579 p = 1) (hb : d171128 p = 1) : d173566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171123 q = 1) : d173561 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171123, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39034 q ha hb
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171124 q = 1) : d173562 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171124, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171125 q = 1) : d173563 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171125, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171126 q = 1) : d173564 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171126, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171127 q = 1) : d173565 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171127, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171128 q = 1) : d173566 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171128, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39036 (p : Pattern) (ha : d128579 p = 1) (hb : d171133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16481 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38741 q ha hb
    | true =>
      simp only [d16481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38742 q ha hb
  have h2 (q : Pattern) (ha : d16482 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16483 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16484 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16485 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171133 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro39037 (p : Pattern) (ha : d128579 p = 1) (hb : d171140 p = 1) : d173570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d128579 q = 1) : d17980 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38777 q ha hb
    | true =>
      simp only [d16673, d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38750 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d128579 q = 1) : d17981 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d128579 q = 1) : d17982 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d128579 q = 1) : d17990 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38750 q ha hb
    | true =>
      simp only [d16676, d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38775 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d128579 q = 1) : d17991 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d128579 q = 1) : d17992 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d128579 q = 1) : d17993 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d128579 q = 1) : d18009 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d18009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38750 q ha hb
    | true =>
      simp only [d16693, d18009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38749 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d128579 q = 1) : d18010 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d18010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d18010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d128579 q = 1) : d18011 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d18011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d18011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d128579 q = 1) : d18012 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171139 q = 1) : d173569 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171139, d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171140 q = 1) : d173570 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171140, d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro39038 (p : Pattern) (ha : d128579 p = 1) (hb : d171146 p = 1) : d173576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171141 q = 1) : d173571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39037 q ha hb
    | true =>
      simp only [d171141, d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171142 q = 1) : d173572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171142, d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d128579 q = 1) : d18015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38751 q ha hb
    | true =>
      simp only [d16699, d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d128579 q = 1) : d18016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171143 q = 1) : d173573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171144 q = 1) : d173574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171145 q = 1) : d173575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171146 q = 1) : d173576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro39039 (p : Pattern) (ha : d128579 p = 1) (hb : d171152 p = 1) : d173582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171147 q = 1) : d173577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39038 q ha hb
    | true =>
      simp only [d171147, d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38752 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171148 q = 1) : d173578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171148, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171149 q = 1) : d173579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171150 q = 1) : d173580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171150, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171151 q = 1) : d173581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171151, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171152 q = 1) : d173582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171152, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39040 (p : Pattern) (ha : d128579 p = 1) (hb : d171158 p = 1) : d173588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16487 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38740 q ha hb
    | true =>
      simp only [d16487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38743 q ha hb
  have h2 (q : Pattern) (ha : d16488 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171131 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171132 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171134 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39036 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171135 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171136 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171137 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128579 q = 1) (hb : d171138 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128579 q = 1) (hb : d171153 q = 1) : d173583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171153, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39039 q ha hb
  have h11 (q : Pattern) (ha : d128579 q = 1) (hb : d171154 q = 1) : d173584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171154, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171155 q = 1) : d173585 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171155, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171156 q = 1) : d173586 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171156, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d128579 q = 1) (hb : d171157 q = 1) : d173587 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171157, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d128579 q = 1) (hb : d171158 q = 1) : d173588 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171158, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39041 (p : Pattern) (ha : d128579 p = 1) (hb : d171164 p = 1) : d173594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171159 q = 1) : d173589 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171159, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39040 q ha hb
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171160 q = 1) : d173590 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171160, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171161 q = 1) : d173591 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171161, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171162 q = 1) : d173592 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171162, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171163 q = 1) : d173593 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171163, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171164 q = 1) : d173594 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171164, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39042 (p : Pattern) (ha : d128579 p = 1) (hb : d171170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16833 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38798 q ha hb
    | true =>
      simp only [d16833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38799 q ha hb
  have h2 (q : Pattern) (ha : d16834 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16835 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16836 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16837 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro39043 (p : Pattern) (ha : d128579 p = 1) (hb : d171177 p = 1) : d173599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d128579 q = 1) : d18161 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38834 q ha hb
    | true =>
      simp only [d17033, d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38807 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d128579 q = 1) : d18162 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d128579 q = 1) : d18163 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d128579 q = 1) : d18171 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38807 q ha hb
    | true =>
      simp only [d17036, d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38832 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d128579 q = 1) : d18172 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d128579 q = 1) : d18173 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d128579 q = 1) : d18174 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d128579 q = 1) : d18192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d18192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38807 q ha hb
    | true =>
      simp only [d17053, d18192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38806 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d128579 q = 1) : d18193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d18193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d18193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d128579 q = 1) : d18194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d18194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d18194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d128579 q = 1) : d18195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171176 q = 1) : d173598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171176, d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171177 q = 1) : d173599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171177, d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171177, d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro39044 (p : Pattern) (ha : d128579 p = 1) (hb : d171183 p = 1) : d173605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171178 q = 1) : d173600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171178, d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39043 q ha hb
    | true =>
      simp only [d171178, d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171179 q = 1) : d173601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171179, d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171179, d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d128579 q = 1) : d18198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38808 q ha hb
    | true =>
      simp only [d17059, d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d128579 q = 1) : d18199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171180 q = 1) : d173602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171180, d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171180, d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171181 q = 1) : d173603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171181, d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171181, d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171182 q = 1) : d173604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171182, d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171182, d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171183 q = 1) : d173605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171183, d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171183, d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro39045 (p : Pattern) (ha : d128579 p = 1) (hb : d171189 p = 1) : d173611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171184 q = 1) : d173606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171184, d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39044 q ha hb
    | true =>
      simp only [d171184, d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38809 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171185 q = 1) : d173607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171185, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171185, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171186 q = 1) : d173608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171186, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171186, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171187 q = 1) : d173609 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171187, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171187, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171188 q = 1) : d173610 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171188, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171188, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171189 q = 1) : d173611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171189, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171189, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39046 (p : Pattern) (ha : d128579 p = 1) (hb : d171195 p = 1) : d173617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16839 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38797 q ha hb
    | true =>
      simp only [d16839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38800 q ha hb
  have h2 (q : Pattern) (ha : d16840 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171168 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171169 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39042 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171172 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171173 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171174 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128579 q = 1) (hb : d171175 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128579 q = 1) (hb : d171190 q = 1) : d173612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171190, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171190, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39045 q ha hb
  have h11 (q : Pattern) (ha : d128579 q = 1) (hb : d171191 q = 1) : d173613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171191, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171191, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171192 q = 1) : d173614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171192, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171192, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171193 q = 1) : d173615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171193, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171193, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d128579 q = 1) (hb : d171194 q = 1) : d173616 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171194, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171194, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d128579 q = 1) (hb : d171195 q = 1) : d173617 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171195, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171195, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39047 (p : Pattern) (ha : d128579 p = 1) (hb : d171201 p = 1) : d173623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171196 q = 1) : d173618 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171196, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171196, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39046 q ha hb
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171197 q = 1) : d173619 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171197, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171197, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171198 q = 1) : d173620 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171198, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171198, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171199 q = 1) : d173621 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171199, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171199, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171200 q = 1) : d173622 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171200, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171200, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171201 q = 1) : d173623 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171201, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171201, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39048 (p : Pattern) (ha : d128579 p = 1) (hb : d171208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17199 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38855 q ha hb
    | true =>
      simp only [d17199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38856 q ha hb
  have h2 (q : Pattern) (ha : d17200 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17201 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17202 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17203 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro39049 (p : Pattern) (ha : d128579 p = 1) (hb : d171215 p = 1) : d173629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d128579 q = 1) : d18342 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38891 q ha hb
    | true =>
      simp only [d17397, d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38864 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d128579 q = 1) : d18343 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d128579 q = 1) : d18344 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d128579 q = 1) : d18352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38864 q ha hb
    | true =>
      simp only [d17400, d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38889 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d128579 q = 1) : d18353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d128579 q = 1) : d18354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d128579 q = 1) : d18355 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d128579 q = 1) : d18373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d18373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38864 q ha hb
    | true =>
      simp only [d17417, d18373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38863 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d128579 q = 1) : d18374 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d18374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d18374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d128579 q = 1) : d18375 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d18375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d18375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d128579 q = 1) : d18376 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171214 q = 1) : d173628 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171214, d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171215 q = 1) : d173629 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171215, d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171215, d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro39050 (p : Pattern) (ha : d128579 p = 1) (hb : d171221 p = 1) : d173635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171216 q = 1) : d173630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171216, d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39049 q ha hb
    | true =>
      simp only [d171216, d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171217 q = 1) : d173631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171217, d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171217, d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d128579 q = 1) : d18379 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38865 q ha hb
    | true =>
      simp only [d17423, d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d128579 q = 1) : d18380 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171218 q = 1) : d173632 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171218, d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171218, d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171219 q = 1) : d173633 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171219, d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171219, d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171220 q = 1) : d173634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171220, d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171220, d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171221 q = 1) : d173635 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171221, d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171221, d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro39051 (p : Pattern) (ha : d128579 p = 1) (hb : d171227 p = 1) : d173641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171222 q = 1) : d173636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171222, d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39050 q ha hb
    | true =>
      simp only [d171222, d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38866 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171223 q = 1) : d173637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171223, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171223, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171224 q = 1) : d173638 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171224, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171224, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171225 q = 1) : d173639 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171225, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171225, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171226 q = 1) : d173640 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171226, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171226, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171227 q = 1) : d173641 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171227, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171227, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39052 (p : Pattern) (ha : d128579 p = 1) (hb : d171233 p = 1) : d173647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17205 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38854 q ha hb
    | true =>
      simp only [d17205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38857 q ha hb
  have h2 (q : Pattern) (ha : d17206 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171206 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171207 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39048 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171211 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128579 q = 1) (hb : d171213 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128579 q = 1) (hb : d171228 q = 1) : d173642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171228, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171228, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39051 q ha hb
  have h11 (q : Pattern) (ha : d128579 q = 1) (hb : d171229 q = 1) : d173643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171229, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171229, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171230 q = 1) : d173644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171230, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171230, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171231 q = 1) : d173645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171231, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171231, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d128579 q = 1) (hb : d171232 q = 1) : d173646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171232, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171232, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d128579 q = 1) (hb : d171233 q = 1) : d173647 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171233, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171233, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39053 (p : Pattern) (ha : d128579 p = 1) (hb : d171239 p = 1) : d173653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171234 q = 1) : d173648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171234, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171234, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39052 q ha hb
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171235 q = 1) : d173649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171235, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171235, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171236 q = 1) : d173650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171236, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171236, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171237 q = 1) : d173651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171237, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171237, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171238 q = 1) : d173652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171238, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171238, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171239 q = 1) : d173653 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171239, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171239, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39054 (p : Pattern) (ha : d128579 p = 1) (hb : d171245 p = 1) : d173659 p = 1 := by
  have h0 (q : Pattern) (ha : d128579 q = 1) (hb : d171102 q = 1) : d173548 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39027 q hb ha
    | true =>
      simp only [d171102, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39031 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171129 q = 1) : d173567 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171129, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39035 q ha hb
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171130 q = 1) : d173568 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171165 q = 1) : d173595 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171165, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39041 q ha hb
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171166 q = 1) : d173596 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171166, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171167 q = 1) : d173597 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128579 q = 1) (hb : d171202 q = 1) : d173624 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171202, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171202, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39047 q ha hb
  have h8 (q : Pattern) (ha : d128579 q = 1) (hb : d171203 q = 1) : d173625 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171203, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171203, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128579 q = 1) (hb : d171204 q = 1) : d173626 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171204, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171204, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128579 q = 1) (hb : d171205 q = 1) : d173627 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171205, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171205, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128579 q = 1) (hb : d171240 q = 1) : d173654 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171240, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171240, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39053 q ha hb
  have h12 (q : Pattern) (ha : d128579 q = 1) (hb : d171241 q = 1) : d173655 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171241, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171241, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128579 q = 1) (hb : d171242 q = 1) : d173656 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171242, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171242, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128579 q = 1) (hb : d171243 q = 1) : d173657 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171243, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171243, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128579 q = 1) (hb : d171244 q = 1) : d173658 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d171244, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171244, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128579 q = 1) (hb : d171245 q = 1) : d173659 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d171245, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d171245, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro39055 (p : Pattern) (ha : d128579 p = 1) (hb : d171251 p = 1) : d173665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171246 q = 1) : d173660 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d171246, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39054 q ha hb
    | true =>
      simp only [d171246, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171247 q = 1) : d173661 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d171247, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171247, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171248 q = 1) : d173662 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d171248, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171248, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171249 q = 1) : d173663 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d171249, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171249, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171250 q = 1) : d173664 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d171250, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171250, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171251 q = 1) : d173665 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d171251, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171251, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39056 (p : Pattern) (ha : d128579 p = 1) (hb : d171257 p = 1) : d173671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171252 q = 1) : d173666 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d171252, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39055 q ha hb
    | true =>
      simp only [d171252, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171253 q = 1) : d173667 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d171253, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171253, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171254 q = 1) : d173668 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d171254, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171254, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171255 q = 1) : d173669 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d171255, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171255, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171256 q = 1) : d173670 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d171256, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171256, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171257 q = 1) : d173671 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d171257, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171257, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39057 (p : Pattern) (ha : d128579 p = 1) (hb : d171263 p = 1) : d173677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171258 q = 1) : d173672 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d171258, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39056 q ha hb
    | true =>
      simp only [d171258, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171259 q = 1) : d173673 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d171259, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171259, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171260 q = 1) : d173674 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d171260, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171260, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171261 q = 1) : d173675 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d171261, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171261, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171262 q = 1) : d173676 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d171262, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171262, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171263 q = 1) : d173677 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d171263, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171263, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39058 (p : Pattern) (ha : d128579 p = 1) (hb : d171269 p = 1) : d173683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171264 q = 1) : d173678 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d171264, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39057 q ha hb
    | true =>
      simp only [d171264, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171265 q = 1) : d173679 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d171265, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171265, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171266 q = 1) : d173680 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d171266, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171266, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171267 q = 1) : d173681 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d171267, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171267, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171268 q = 1) : d173682 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d171268, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171268, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171269 q = 1) : d173683 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d171269, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171269, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39059 (p : Pattern) (ha : d128579 p = 1) (hb : d171275 p = 1) : d173689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171270 q = 1) : d173684 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d171270, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39058 q ha hb
    | true =>
      simp only [d171270, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171271 q = 1) : d173685 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d171271, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171271, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171272 q = 1) : d173686 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d171272, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171272, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171273 q = 1) : d173687 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d171273, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171273, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171274 q = 1) : d173688 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d171274, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171274, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171275 q = 1) : d173689 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d171275, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171275, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39060 (p : Pattern) (ha : d128579 p = 1) (hb : d171281 p = 1) : d173695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171276 q = 1) : d173690 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d171276, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39059 q ha hb
    | true =>
      simp only [d171276, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171277 q = 1) : d173691 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d171277, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171277, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171278 q = 1) : d173692 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d171278, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171278, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171279 q = 1) : d173693 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d171279, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171279, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171280 q = 1) : d173694 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d171280, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171280, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171281 q = 1) : d173695 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d171281, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171281, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39061 (p : Pattern) (ha : d128579 p = 1) (hb : d171287 p = 1) : d173701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128579 q = 1) (hb : d171282 q = 1) : d173696 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d171282, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39060 q ha hb
    | true =>
      simp only [d171282, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128579 q = 1) (hb : d171283 q = 1) : d173697 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d171283, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171283, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128579 q = 1) (hb : d171284 q = 1) : d173698 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d171284, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171284, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128579 q = 1) (hb : d171285 q = 1) : d173699 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d171285, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171285, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128579 q = 1) (hb : d171286 q = 1) : d173700 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d171286, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171286, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128579 q = 1) (hb : d171287 q = 1) : d173701 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d171287, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171287, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39062 (p : Pattern) (ha : d17696 p = 1) (hb : d128634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17577 q = 1) (hb : d128597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d128597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38913 q ha hb
    | true =>
      simp only [d17577, d128597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17692 q = 1) (hb : d128630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, d128630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17692, d128630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128598 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17693 q = 1) (hb : d128631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, d128631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17693, d128631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17694 q = 1) (hb : d128632 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, d128632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17694, d128632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17695 q = 1) (hb : d128633 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, d128633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17695, d128633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17696 q = 1) (hb : d128634 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, d128634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17696, d128634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39063 (p : Pattern) (ha : d61083 p = 1) (hb : d128640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17697 q = 1) (hb : d128635 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, d128635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, d128635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39062 q ha hb
  have h2 (q : Pattern) (ha : d61079 q = 1) (hb : d128636 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61079, d128636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61079, d128636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61080 q = 1) (hb : d128637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61080, d128637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61080, d128637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61081 q = 1) (hb : d128638 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61081, d128638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61081, d128638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61082 q = 1) (hb : d128639 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61082, d128639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61082, d128639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61083 q = 1) (hb : d128640 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61083, d128640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61083, d128640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39064 (p : Pattern) (ha : d61093 p = 1) (hb : d128676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128665 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17609 q = 1) (hb : d128629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, d128629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38918 q ha hb
    | true =>
      simp only [d17609, d128629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38913 q ha hb
  have h3 (q : Pattern) (ha : d61089 q = 1) (hb : d128666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d61089, d128666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61089, d128666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128672 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61090 q = 1) (hb : d128673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d61090, d128673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61090, d128673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61091 q = 1) (hb : d128674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d61091, d128674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61091, d128674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61092 q = 1) (hb : d128675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d61092, d128675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61092, d128675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61093 q = 1) (hb : d128676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d61093, d128676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61093, d128676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39065 (p : Pattern) (ha : d61099 p = 1) (hb : d128688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61094 q = 1) (hb : d128677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61094, d128677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61094, d128677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39064 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61095 q = 1) (hb : d128684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61095, d128684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61095, d128684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61096 q = 1) (hb : d128685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61096, d128685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61096, d128685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61097 q = 1) (hb : d128686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61097, d128686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61097, d128686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61098 q = 1) (hb : d128687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61098, d128687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61098, d128687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61099 q = 1) (hb : d128688 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61099, d128688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61099, d128688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39066 (p : Pattern) (ha : d61105 p = 1) (hb : d128694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128612 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61084 q = 1) (hb : d128641 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61084, d128641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61084, d128641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39063 q ha hb
  have h3 (q : Pattern) (ha : d61085 q = 1) (hb : d128642 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61085, d128642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61085, d128642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61086 q = 1) (hb : d128643 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61086, d128643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61086, d128643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61087 q = 1) (hb : d128644 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61087, d128644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61087, d128644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61088 q = 1) (hb : d128645 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61088, d128645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61088, d128645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61100 q = 1) (hb : d128689 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61100, d128689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61100, d128689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39065 q ha hb
  have h8 (q : Pattern) (ha : d61101 q = 1) (hb : d128690 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61101, d128690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61101, d128690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61102 q = 1) (hb : d128691 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61102, d128691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61102, d128691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61103 q = 1) (hb : d128692 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61103, d128692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61103, d128692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61104 q = 1) (hb : d128693 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61104, d128693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61104, d128693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61105 q = 1) (hb : d128694 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61105, d128694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61105, d128694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39067 (p : Pattern) (ha : d128749 p = 1) (hb : d173535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128733 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128738 q = 1) (hb : d173530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128738, d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38937 q hb ha
    | true =>
      simp only [d128738, d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38930 q hb ha
  have h3 (q : Pattern) (ha : d128739 q = 1) (hb : d173531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128739, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128739, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128745 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128746 q = 1) (hb : d173532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128746, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128746, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128747 q = 1) (hb : d173533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128747, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128747, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128748 q = 1) (hb : d173534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128748, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128748, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128749 q = 1) (hb : d173535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128749, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128749, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39068 (p : Pattern) (ha : d128762 p = 1) (hb : d173541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128750 q = 1) (hb : d173536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128750, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128750, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39067 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128758 q = 1) (hb : d173537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128758, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128758, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128759 q = 1) (hb : d173538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128759, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128759, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128760 q = 1) (hb : d173539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128760, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128760, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128761 q = 1) (hb : d173540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128761, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128761, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128762 q = 1) (hb : d173541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128762, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128762, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39069 (p : Pattern) (ha : d128768 p = 1) (hb : d173547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128763 q = 1) (hb : d173542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128763, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128763, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39068 q ha hb
  have h2 (q : Pattern) (ha : d128764 q = 1) (hb : d173543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128764, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128764, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128765 q = 1) (hb : d173544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128765, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128765, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128766 q = 1) (hb : d173545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128766, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128766, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128767 q = 1) (hb : d173546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128767, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128767, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128768 q = 1) (hb : d173547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128768, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128768, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39070 (p : Pattern) (ha : d128839 p = 1) (hb : d173554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128823 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128828 q = 1) (hb : d173549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128828, d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38953 q hb ha
    | true =>
      simp only [d128828, d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38945 q hb ha
  have h3 (q : Pattern) (ha : d128829 q = 1) (hb : d173550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128829, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128829, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128836 q = 1) (hb : d173551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128836, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128836, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128837 q = 1) (hb : d173552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128837, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128837, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128838 q = 1) (hb : d173553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128838, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128838, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128839 q = 1) (hb : d173554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128839, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128839, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39071 (p : Pattern) (ha : d128852 p = 1) (hb : d173560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128840 q = 1) (hb : d173555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128840, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128840, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39070 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128847 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128848 q = 1) (hb : d173556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128848, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128848, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128849 q = 1) (hb : d173557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128849, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128849, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128850 q = 1) (hb : d173558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128850, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128850, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128851 q = 1) (hb : d173559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128851, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128851, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128852 q = 1) (hb : d173560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128852, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128852, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39072 (p : Pattern) (ha : d128858 p = 1) (hb : d173566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128853 q = 1) (hb : d173561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128853, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128853, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39071 q ha hb
  have h2 (q : Pattern) (ha : d128854 q = 1) (hb : d173562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128854, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128854, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128855 q = 1) (hb : d173563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128855, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128855, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128856 q = 1) (hb : d173564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128856, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128856, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128857 q = 1) (hb : d173565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128857, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128857, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128858 q = 1) (hb : d173566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128858, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128858, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39073 (p : Pattern) (ha : d128942 p = 1) (hb : d173570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d128899 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d128899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38964 q ha hb
    | true =>
      simp only [d17980, d128899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38958 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d128900 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d128900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d128900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d128901 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d128901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d128901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d128909 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d128909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38958 q ha hb
    | true =>
      simp only [d17990, d128909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38966 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d128910 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d128910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d128910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d128911 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d128911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d128911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d128912 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d128912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d128912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18009 q = 1) (hb : d128928 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, d128928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38958 q ha hb
    | true =>
      simp only [d18009, d128928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38959 q ha hb
  have h9 (q : Pattern) (ha : d18010 q = 1) (hb : d128929 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, d128929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, d128929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18011 q = 1) (hb : d128930 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d128930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d128930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18012 q = 1) (hb : d128931 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, d128931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18012, d128931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128941 q = 1) (hb : d173569 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128941, d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128941, d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d128942 q = 1) (hb : d173570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128942, d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128942, d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro39074 (p : Pattern) (ha : d128948 p = 1) (hb : d173576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128943 q = 1) (hb : d173571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128943, d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39073 q ha hb
    | true =>
      simp only [d128943, d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128944 q = 1) (hb : d173572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128944, d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128944, d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d128934 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d128934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38960 q ha hb
    | true =>
      simp only [d18015, d128934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d128935 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d128935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d128935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128945 q = 1) (hb : d173573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128945, d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128945, d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128946 q = 1) (hb : d173574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128946, d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128946, d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128947 q = 1) (hb : d173575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128947, d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128947, d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128948 q = 1) (hb : d173576 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128948, d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128948, d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro39075 (p : Pattern) (ha : d128973 p = 1) (hb : d173582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128940 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128953 q = 1) (hb : d173577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128953, d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39074 q ha hb
    | true =>
      simp only [d128953, d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38961 q hb ha
  have h3 (q : Pattern) (ha : d128954 q = 1) (hb : d173578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128954, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128954, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128969 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128970 q = 1) (hb : d173579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128970, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128970, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128971 q = 1) (hb : d173580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128971, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128971, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128972 q = 1) (hb : d173581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128972, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128972, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128973 q = 1) (hb : d173582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128973, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128973, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39076 (p : Pattern) (ha : d128986 p = 1) (hb : d173588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128974 q = 1) (hb : d173583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128974, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128974, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39075 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128982 q = 1) (hb : d173584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128982, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128982, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128983 q = 1) (hb : d173585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128983, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128983, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128984 q = 1) (hb : d173586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128984, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128984, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128985 q = 1) (hb : d173587 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128985, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128985, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128986 q = 1) (hb : d173588 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128986, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128986, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39077 (p : Pattern) (ha : d128992 p = 1) (hb : d173594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128987 q = 1) (hb : d173589 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128987, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128987, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39076 q ha hb
  have h2 (q : Pattern) (ha : d128988 q = 1) (hb : d173590 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128988, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128988, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128989 q = 1) (hb : d173591 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128989, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128989, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128990 q = 1) (hb : d173592 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128990, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128990, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128991 q = 1) (hb : d173593 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128991, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128991, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128992 q = 1) (hb : d173594 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128992, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128992, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39078 (p : Pattern) (ha : d129079 p = 1) (hb : d173599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d129034 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d129034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38983 q ha hb
    | true =>
      simp only [d18161, d129034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38977 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d129035 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d129035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d129035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d129036 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d129036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d129036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d129044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d129044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38977 q ha hb
    | true =>
      simp only [d18171, d129044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38985 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d129045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d129045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d129045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d129046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d129046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d129046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d129047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d129047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d129047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18192 q = 1) (hb : d129065 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, d129065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38977 q ha hb
    | true =>
      simp only [d18192, d129065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38978 q ha hb
  have h9 (q : Pattern) (ha : d18193 q = 1) (hb : d129066 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, d129066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, d129066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18194 q = 1) (hb : d129067 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d129067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d129067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18195 q = 1) (hb : d129068 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, d129068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18195, d129068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d129078 q = 1) (hb : d173598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129078, d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d129078, d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d129079 q = 1) (hb : d173599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129079, d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d129079, d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro39079 (p : Pattern) (ha : d129085 p = 1) (hb : d173605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129080 q = 1) (hb : d173600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129080, d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39078 q ha hb
    | true =>
      simp only [d129080, d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129081 q = 1) (hb : d173601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129081, d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129081, d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d129071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d129071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38979 q ha hb
    | true =>
      simp only [d18198, d129071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d129072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d129072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d129072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129082 q = 1) (hb : d173602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129082, d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129082, d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129083 q = 1) (hb : d173603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129083, d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129083, d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129084 q = 1) (hb : d173604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129084, d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129084, d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129085 q = 1) (hb : d173605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129085, d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129085, d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro39080 (p : Pattern) (ha : d129110 p = 1) (hb : d173611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129077 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129090 q = 1) (hb : d173606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129090, d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39079 q ha hb
    | true =>
      simp only [d129090, d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38980 q hb ha
  have h3 (q : Pattern) (ha : d129091 q = 1) (hb : d173607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129091, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129091, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129106 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129107 q = 1) (hb : d173608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129107, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129107, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129108 q = 1) (hb : d173609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129108, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129108, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129109 q = 1) (hb : d173610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129109, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129109, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129110 q = 1) (hb : d173611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129110, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129110, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39081 (p : Pattern) (ha : d129123 p = 1) (hb : d173617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129111 q = 1) (hb : d173612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129111, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129111, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39080 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129119 q = 1) (hb : d173613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129119, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129119, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129120 q = 1) (hb : d173614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129120, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129120, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129121 q = 1) (hb : d173615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129121, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129121, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129122 q = 1) (hb : d173616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129122, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129122, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129123 q = 1) (hb : d173617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129123, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129123, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39082 (p : Pattern) (ha : d129129 p = 1) (hb : d173623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129124 q = 1) (hb : d173618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129124, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129124, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39081 q ha hb
  have h2 (q : Pattern) (ha : d129125 q = 1) (hb : d173619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129125, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129125, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129126 q = 1) (hb : d173620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129126, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129126, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129127 q = 1) (hb : d173621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129127, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129127, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129128 q = 1) (hb : d173622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129128, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129128, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129129 q = 1) (hb : d173623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129129, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129129, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39083 (p : Pattern) (ha : d129212 p = 1) (hb : d173629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d129167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d129167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39002 q ha hb
    | true =>
      simp only [d18342, d129167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d129168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d129168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d129168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d129169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d129169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d129169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d129177 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d129177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
    | true =>
      simp only [d18352, d129177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39004 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d129178 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d129178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d129178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d129179 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d129179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d129179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d129180 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d129180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d129180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18373 q = 1) (hb : d129198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, d129198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38996 q ha hb
    | true =>
      simp only [d18373, d129198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38997 q ha hb
  have h9 (q : Pattern) (ha : d18374 q = 1) (hb : d129199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, d129199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, d129199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18375 q = 1) (hb : d129200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d129200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d129200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18376 q = 1) (hb : d129201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, d129201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18376, d129201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d129211 q = 1) (hb : d173628 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129211, d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d129211, d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d129212 q = 1) (hb : d173629 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129212, d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d129212, d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro39084 (p : Pattern) (ha : d129218 p = 1) (hb : d173635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129213 q = 1) (hb : d173630 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129213, d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39083 q ha hb
    | true =>
      simp only [d129213, d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129214 q = 1) (hb : d173631 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129214, d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129214, d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d129204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d129204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38998 q ha hb
    | true =>
      simp only [d18379, d129204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d129205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d129205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d129205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129215 q = 1) (hb : d173632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129215, d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129215, d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129216 q = 1) (hb : d173633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129216, d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129216, d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129217 q = 1) (hb : d173634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129217, d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129217, d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129218 q = 1) (hb : d173635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129218, d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129218, d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro39085 (p : Pattern) (ha : d129243 p = 1) (hb : d173641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129210 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129223 q = 1) (hb : d173636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129223, d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39084 q ha hb
    | true =>
      simp only [d129223, d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38999 q hb ha
  have h3 (q : Pattern) (ha : d129224 q = 1) (hb : d173637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129224, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129224, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129239 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129240 q = 1) (hb : d173638 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129240, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129240, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129241 q = 1) (hb : d173639 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129241, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129241, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129242 q = 1) (hb : d173640 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129242, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129242, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129243 q = 1) (hb : d173641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129243, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129243, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39086 (p : Pattern) (ha : d129256 p = 1) (hb : d173647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129244 q = 1) (hb : d173642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129244, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129244, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39085 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129251 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129252 q = 1) (hb : d173643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129252, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129252, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129253 q = 1) (hb : d173644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129253, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129253, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129254 q = 1) (hb : d173645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129254, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129254, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129255 q = 1) (hb : d173646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129255, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129255, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129256 q = 1) (hb : d173647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129256, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129256, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39087 (p : Pattern) (ha : d129262 p = 1) (hb : d173653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129257 q = 1) (hb : d173648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129257, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129257, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39086 q ha hb
  have h2 (q : Pattern) (ha : d129258 q = 1) (hb : d173649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129258, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129258, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129259 q = 1) (hb : d173650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129259, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129259, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129260 q = 1) (hb : d173651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129260, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129260, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129261 q = 1) (hb : d173652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129261, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129261, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129262 q = 1) (hb : d173653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129262, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129262, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39088 (p : Pattern) (ha : d129268 p = 1) (hb : d173659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128769 q = 1) (hb : d173548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128769, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39066 q hb ha
    | true =>
      simp only [d128769, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39069 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128859 q = 1) (hb : d173567 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128859, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128859, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39072 q ha hb
  have h3 (q : Pattern) (ha : d128860 q = 1) (hb : d173568 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128860, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128860, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128993 q = 1) (hb : d173595 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128993, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128993, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39077 q ha hb
  have h5 (q : Pattern) (ha : d128994 q = 1) (hb : d173596 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128994, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128994, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128995 q = 1) (hb : d173597 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128995, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128995, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129130 q = 1) (hb : d173624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129130, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129130, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39082 q ha hb
  have h8 (q : Pattern) (ha : d129131 q = 1) (hb : d173625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129131, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129131, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129132 q = 1) (hb : d173626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129132, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129132, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129133 q = 1) (hb : d173627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129133, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129133, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129263 q = 1) (hb : d173654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129263, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129263, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39087 q ha hb
  have h12 (q : Pattern) (ha : d129264 q = 1) (hb : d173655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129264, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129264, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129265 q = 1) (hb : d173656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129265, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129265, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129266 q = 1) (hb : d173657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129266, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129266, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129267 q = 1) (hb : d173658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129267, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129267, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129268 q = 1) (hb : d173659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129268, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129268, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro39089 (p : Pattern) (ha : d129274 p = 1) (hb : d173665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129269 q = 1) (hb : d173660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129269, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39088 q ha hb
    | true =>
      simp only [d129269, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129270 q = 1) (hb : d173661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129270, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129270, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129271 q = 1) (hb : d173662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129271, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129271, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129272 q = 1) (hb : d173663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129272, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129272, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129273 q = 1) (hb : d173664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129273, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129273, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129274 q = 1) (hb : d173665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129274, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129274, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39090 (p : Pattern) (ha : d129280 p = 1) (hb : d173671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129275 q = 1) (hb : d173666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129275, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39089 q ha hb
    | true =>
      simp only [d129275, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129276 q = 1) (hb : d173667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129276, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129276, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129277 q = 1) (hb : d173668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129277, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129277, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129278 q = 1) (hb : d173669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129278, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129278, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129279 q = 1) (hb : d173670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129279, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129279, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129280 q = 1) (hb : d173671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129280, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129280, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39091 (p : Pattern) (ha : d129286 p = 1) (hb : d173677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129281 q = 1) (hb : d173672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129281, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39090 q ha hb
    | true =>
      simp only [d129281, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129282 q = 1) (hb : d173673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129282, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129282, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129283 q = 1) (hb : d173674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129283, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129283, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129284 q = 1) (hb : d173675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129284, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129284, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129285 q = 1) (hb : d173676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129285, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129285, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129286 q = 1) (hb : d173677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129286, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129286, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39092 (p : Pattern) (ha : d129292 p = 1) (hb : d173683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129287 q = 1) (hb : d173678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129287, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39091 q ha hb
    | true =>
      simp only [d129287, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129288 q = 1) (hb : d173679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129288, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129288, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129289 q = 1) (hb : d173680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129289, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129289, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129290 q = 1) (hb : d173681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129290, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129290, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129291 q = 1) (hb : d173682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129291, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129291, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129292 q = 1) (hb : d173683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129292, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129292, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39093 (p : Pattern) (ha : d129298 p = 1) (hb : d173689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129293 q = 1) (hb : d173684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129293, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39092 q ha hb
    | true =>
      simp only [d129293, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129294 q = 1) (hb : d173685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129294, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129294, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129295 q = 1) (hb : d173686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129295, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129295, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129296 q = 1) (hb : d173687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129296, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129296, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129297 q = 1) (hb : d173688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129297, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129297, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129298 q = 1) (hb : d173689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129298, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129298, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39094 (p : Pattern) (ha : d129304 p = 1) (hb : d173695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129299 q = 1) (hb : d173690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129299, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39093 q ha hb
    | true =>
      simp only [d129299, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129300 q = 1) (hb : d173691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129300, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129300, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129301 q = 1) (hb : d173692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129301, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129301, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129302 q = 1) (hb : d173693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129302, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129302, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129303 q = 1) (hb : d173694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129303, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129303, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129304 q = 1) (hb : d173695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129304, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129304, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39095 (p : Pattern) (ha : d129310 p = 1) (hb : d173701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129305 q = 1) (hb : d173696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129305, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39094 q ha hb
    | true =>
      simp only [d129305, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129306 q = 1) (hb : d173697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129306, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129306, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129307 q = 1) (hb : d173698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129307, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129307, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129308 q = 1) (hb : d173699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129308, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129308, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129309 q = 1) (hb : d173700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129309, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129309, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129310 q = 1) (hb : d173701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129310, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129310, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro39096 (p : Pattern) (ha : d17696 p = 1) (hb : d60563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d17692 q = 1) (hb : d60559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17692, d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17578 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17693 q = 1) (hb : d60560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17693, d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17694 q = 1) (hb : d60561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17694, d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17695 q = 1) (hb : d60562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17695, d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17696 q = 1) (hb : d60563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17696, d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39097 (p : Pattern) (ha : d60569 p = 1) (hb : d61083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17697 q = 1) (hb : d60564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39096 q ha hb
  have h2 (q : Pattern) (ha : d60565 q = 1) (hb : d61079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d60565, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60565, d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d60566 q = 1) (hb : d61080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d60566, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60566, d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d60567 q = 1) (hb : d61081 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d60567, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60567, d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60568 q = 1) (hb : d61082 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d60568, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60568, d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d60569 q = 1) (hb : d61083 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60569, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60569, d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39098 (p : Pattern) (ha : d61093 p = 1) (hb : d129315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17609 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61089 q = 1) (hb : d129311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d61089, d129311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61089, d129311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61090 q = 1) (hb : d129312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d61090, d129312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61090, d129312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61091 q = 1) (hb : d129313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d61091, d129313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61091, d129313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61092 q = 1) (hb : d129314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d61092, d129314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61092, d129314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61093 q = 1) (hb : d129315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d61093, d129315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61093, d129315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39099 (p : Pattern) (ha : d61099 p = 1) (hb : d129321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61094 q = 1) (hb : d129316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61094, d129316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61094, d129316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39098 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61095 q = 1) (hb : d129317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61095, d129317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61095, d129317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61096 q = 1) (hb : d129318 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61096, d129318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61096, d129318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61097 q = 1) (hb : d129319 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61097, d129319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61097, d129319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61098 q = 1) (hb : d129320 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61098, d129320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61098, d129320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61099 q = 1) (hb : d129321 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61099, d129321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61099, d129321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39100 (p : Pattern) (ha : d61105 p = 1) (hb : d129327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17592 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d60570 q = 1) (hb : d61084 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60570, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60570, d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39097 q ha hb
  have h3 (q : Pattern) (ha : d60571 q = 1) (hb : d61085 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60571, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60571, d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60572 q = 1) (hb : d61086 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60572, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60572, d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60573 q = 1) (hb : d61087 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60573, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60573, d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60574 q = 1) (hb : d61088 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60574, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60574, d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61100 q = 1) (hb : d129322 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61100, d129322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61100, d129322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39099 q ha hb
  have h8 (q : Pattern) (ha : d61101 q = 1) (hb : d129323 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61101, d129323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61101, d129323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61102 q = 1) (hb : d129324 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61102, d129324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61102, d129324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61103 q = 1) (hb : d129325 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61103, d129325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61103, d129325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61104 q = 1) (hb : d129326 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61104, d129326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61104, d129326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61105 q = 1) (hb : d129327 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61105, d129327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d61105, d129327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39101 (p : Pattern) (ha : d129332 p = 1) (hb : d173535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173530 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129328 q = 1) (hb : d173531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129328, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129328, d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17783 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129329 q = 1) (hb : d173532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129329, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129329, d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129330 q = 1) (hb : d173533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129330, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129330, d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129331 q = 1) (hb : d173534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129331, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129331, d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129332 q = 1) (hb : d173535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129332, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129332, d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39102 (p : Pattern) (ha : d129338 p = 1) (hb : d173541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129333 q = 1) (hb : d173536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129333, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129333, d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39101 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17799 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129334 q = 1) (hb : d173537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129334, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129334, d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129335 q = 1) (hb : d173538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129335, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129335, d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129336 q = 1) (hb : d173539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129336, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129336, d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129337 q = 1) (hb : d173540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129337, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129337, d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129338 q = 1) (hb : d173541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129338, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129338, d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39103 (p : Pattern) (ha : d129344 p = 1) (hb : d173547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129339 q = 1) (hb : d173542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129339, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129339, d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39102 q ha hb
  have h2 (q : Pattern) (ha : d129340 q = 1) (hb : d173543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129340, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129340, d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129341 q = 1) (hb : d173544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129341, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129341, d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129342 q = 1) (hb : d173545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129342, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129342, d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129343 q = 1) (hb : d173546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129343, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129343, d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129344 q = 1) (hb : d173547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129344, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129344, d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39104 (p : Pattern) (ha : d129350 p = 1) (hb : d173554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17865 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129346 q = 1) (hb : d173550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129346, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129346, d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17912 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129347 q = 1) (hb : d173551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129347, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129347, d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129348 q = 1) (hb : d173552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129348, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129348, d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129349 q = 1) (hb : d173553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129349, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129349, d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129350 q = 1) (hb : d173554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129350, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129350, d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39105 (p : Pattern) (ha : d129356 p = 1) (hb : d173560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129351 q = 1) (hb : d173555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129351, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129351, d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39104 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129352 q = 1) (hb : d173556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129352, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129352, d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129353 q = 1) (hb : d173557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129353, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129353, d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129354 q = 1) (hb : d173558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129354, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129354, d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129355 q = 1) (hb : d173559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129355, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129355, d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129356 q = 1) (hb : d173560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129356, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129356, d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39106 (p : Pattern) (ha : d129362 p = 1) (hb : d173566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129357 q = 1) (hb : d173561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129357, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129357, d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39105 q ha hb
  have h2 (q : Pattern) (ha : d129358 q = 1) (hb : d173562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129358, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129358, d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129359 q = 1) (hb : d173563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129359, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129359, d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129360 q = 1) (hb : d173564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129360, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129360, d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129361 q = 1) (hb : d173565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129361, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129361, d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129362 q = 1) (hb : d173566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129362, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129362, d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39107 (p : Pattern) (ha : d129369 p = 1) (hb : d173582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18021 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129365 q = 1) (hb : d173578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129365, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129365, d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18092 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129366 q = 1) (hb : d173579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129366, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129366, d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129367 q = 1) (hb : d173580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129367, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129367, d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129368 q = 1) (hb : d173581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129368, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129368, d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129369 q = 1) (hb : d173582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129369, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129369, d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39108 (p : Pattern) (ha : d129375 p = 1) (hb : d173588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129370 q = 1) (hb : d173583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129370, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129370, d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39107 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129371 q = 1) (hb : d173584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129371, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129371, d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129372 q = 1) (hb : d173585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129372, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129372, d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129373 q = 1) (hb : d173586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129373, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129373, d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129374 q = 1) (hb : d173587 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129374, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129374, d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129375 q = 1) (hb : d173588 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129375, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129375, d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39109 (p : Pattern) (ha : d129381 p = 1) (hb : d173594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129376 q = 1) (hb : d173589 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129376, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129376, d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39108 q ha hb
  have h2 (q : Pattern) (ha : d129377 q = 1) (hb : d173590 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129377, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129377, d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129378 q = 1) (hb : d173591 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129378, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129378, d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129379 q = 1) (hb : d173592 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129379, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129379, d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129380 q = 1) (hb : d173593 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129380, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129380, d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129381 q = 1) (hb : d173594 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129381, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129381, d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39110 (p : Pattern) (ha : d129389 p = 1) (hb : d173611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173606 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129385 q = 1) (hb : d173607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129385, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129385, d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18277 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129386 q = 1) (hb : d173608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129386, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129386, d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129387 q = 1) (hb : d173609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129387, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129387, d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129388 q = 1) (hb : d173610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129388, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129388, d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129389 q = 1) (hb : d173611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129389, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129389, d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39111 (p : Pattern) (ha : d129395 p = 1) (hb : d173617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129390 q = 1) (hb : d173612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129390, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129390, d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39110 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18293 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129391 q = 1) (hb : d173613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129391, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129391, d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129392 q = 1) (hb : d173614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129392, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129392, d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129393 q = 1) (hb : d173615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129393, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129393, d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129394 q = 1) (hb : d173616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129394, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129394, d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129395 q = 1) (hb : d173617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129395, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129395, d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39112 (p : Pattern) (ha : d129401 p = 1) (hb : d173623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129396 q = 1) (hb : d173618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129396, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129396, d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39111 q ha hb
  have h2 (q : Pattern) (ha : d129397 q = 1) (hb : d173619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129397, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129397, d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129398 q = 1) (hb : d173620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129398, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129398, d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129399 q = 1) (hb : d173621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129399, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129399, d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129400 q = 1) (hb : d173622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129400, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129400, d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129401 q = 1) (hb : d173623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129401, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129401, d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39113 (p : Pattern) (ha : d129410 p = 1) (hb : d173641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18385 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d173636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129406 q = 1) (hb : d173637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129406, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129406, d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18458 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129407 q = 1) (hb : d173638 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129407, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129407, d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129408 q = 1) (hb : d173639 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129408, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129408, d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129409 q = 1) (hb : d173640 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129409, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129409, d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129410 q = 1) (hb : d173641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129410, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129410, d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39114 (p : Pattern) (ha : d129416 p = 1) (hb : d173647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129411 q = 1) (hb : d173642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129411, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129411, d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39113 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129412 q = 1) (hb : d173643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129412, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129412, d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129413 q = 1) (hb : d173644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129413, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129413, d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129414 q = 1) (hb : d173645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129414, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129414, d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129415 q = 1) (hb : d173646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129415, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129415, d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129416 q = 1) (hb : d173647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129416, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129416, d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39115 (p : Pattern) (ha : d129422 p = 1) (hb : d173653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129417 q = 1) (hb : d173648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129417, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129417, d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39114 q ha hb
  have h2 (q : Pattern) (ha : d129418 q = 1) (hb : d173649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129418, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129418, d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129419 q = 1) (hb : d173650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129419, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129419, d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129420 q = 1) (hb : d173651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129420, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129420, d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129421 q = 1) (hb : d173652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129421, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129421, d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129422 q = 1) (hb : d173653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129422, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129422, d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39116 (p : Pattern) (ha : d129428 p = 1) (hb : d173659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129345 q = 1) (hb : d173548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129345, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39100 q hb ha
    | true =>
      simp only [d129345, d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39103 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129363 q = 1) (hb : d173567 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129363, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129363, d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39106 q ha hb
  have h3 (q : Pattern) (ha : d129364 q = 1) (hb : d173568 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129364, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129364, d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129382 q = 1) (hb : d173595 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129382, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129382, d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39109 q ha hb
  have h5 (q : Pattern) (ha : d129383 q = 1) (hb : d173596 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129383, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129383, d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129384 q = 1) (hb : d173597 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129384, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129384, d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129402 q = 1) (hb : d173624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129402, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129402, d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39112 q ha hb
  have h8 (q : Pattern) (ha : d129403 q = 1) (hb : d173625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129403, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129403, d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129404 q = 1) (hb : d173626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129404, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129404, d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129405 q = 1) (hb : d173627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129405, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129405, d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129423 q = 1) (hb : d173654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129423, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129423, d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39115 q ha hb
  have h12 (q : Pattern) (ha : d129424 q = 1) (hb : d173655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129424, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129424, d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129425 q = 1) (hb : d173656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129425, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129425, d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129426 q = 1) (hb : d173657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129426, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129426, d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129427 q = 1) (hb : d173658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129427, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129427, d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129428 q = 1) (hb : d173659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129428, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129428, d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro39117 (p : Pattern) (ha : d129434 p = 1) (hb : d173665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129429 q = 1) (hb : d173660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129429, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39116 q ha hb
    | true =>
      simp only [d129429, d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129430 q = 1) (hb : d173661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129430, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129430, d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129431 q = 1) (hb : d173662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129431, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129431, d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129432 q = 1) (hb : d173663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129432, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129432, d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129433 q = 1) (hb : d173664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129433, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129433, d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129434 q = 1) (hb : d173665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129434, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129434, d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39118 (p : Pattern) (ha : d129440 p = 1) (hb : d173671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129435 q = 1) (hb : d173666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129435, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39117 q ha hb
    | true =>
      simp only [d129435, d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129436 q = 1) (hb : d173667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129436, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129436, d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129437 q = 1) (hb : d173668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129437, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129437, d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129438 q = 1) (hb : d173669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129438, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129438, d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129439 q = 1) (hb : d173670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129439, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129439, d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129440 q = 1) (hb : d173671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129440, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129440, d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39119 (p : Pattern) (ha : d129446 p = 1) (hb : d173677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129441 q = 1) (hb : d173672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129441, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39118 q ha hb
    | true =>
      simp only [d129441, d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129442 q = 1) (hb : d173673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129442, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129442, d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129443 q = 1) (hb : d173674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129443, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129443, d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129444 q = 1) (hb : d173675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129444, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129444, d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129445 q = 1) (hb : d173676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129445, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129445, d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129446 q = 1) (hb : d173677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129446, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129446, d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39120 (p : Pattern) (ha : d129452 p = 1) (hb : d173683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129447 q = 1) (hb : d173678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129447, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39119 q ha hb
    | true =>
      simp only [d129447, d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129448 q = 1) (hb : d173679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129448, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129448, d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129449 q = 1) (hb : d173680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129449, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129449, d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129450 q = 1) (hb : d173681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129450, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129450, d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129451 q = 1) (hb : d173682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129451, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129451, d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129452 q = 1) (hb : d173683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129452, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129452, d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39121 (p : Pattern) (ha : d129458 p = 1) (hb : d173689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129453 q = 1) (hb : d173684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129453, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39120 q ha hb
    | true =>
      simp only [d129453, d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129454 q = 1) (hb : d173685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129454, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129454, d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129455 q = 1) (hb : d173686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129455, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129455, d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129456 q = 1) (hb : d173687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129456, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129456, d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129457 q = 1) (hb : d173688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129457, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129457, d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129458 q = 1) (hb : d173689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129458, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129458, d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39122 (p : Pattern) (ha : d129464 p = 1) (hb : d173695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129459 q = 1) (hb : d173690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129459, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39121 q ha hb
    | true =>
      simp only [d129459, d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129460 q = 1) (hb : d173691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129460, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129460, d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129461 q = 1) (hb : d173692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129461, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129461, d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129462 q = 1) (hb : d173693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129462, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129462, d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129463 q = 1) (hb : d173694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129463, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129463, d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129464 q = 1) (hb : d173695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129464, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129464, d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39123 (p : Pattern) (ha : d129470 p = 1) (hb : d173701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129465 q = 1) (hb : d173696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129465, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39122 q ha hb
    | true =>
      simp only [d129465, d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129466 q = 1) (hb : d173697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129466, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129466, d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129467 q = 1) (hb : d173698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129467, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129467, d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129468 q = 1) (hb : d173699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129468, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129468, d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129469 q = 1) (hb : d173700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129469, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129469, d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129470 q = 1) (hb : d173701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129470, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129470, d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39124 (p : Pattern) (ha : d71 p = 1) (hb : d173704 p = 1) : d30 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26 q = 1) (hb : d131097 q = 1) : d26 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68 q = 1) (hb : d173703 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69 q = 1) (hb : d173704 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d70 q = 1) (hb : d173704 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71 q = 1) (hb : d173704 q = 1) : d30 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71, d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro39125 (p : Pattern) (ha : d77 p = 1) (hb : d173704 p = 1) : d36 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d173704 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39124 q ha hb
    | true =>
      simp only [d72, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d173704 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d173704 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d173704 q = 1) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d173704 q = 1) : d35 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d173704 q = 1) : d36 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39126 (p : Pattern) (ha : d83 p = 1) (hb : d173704 p = 1) : d49 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d173704 q = 1) : d37 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39125 q ha hb
    | true =>
      simp only [d78, d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d173704 q = 1) : d38 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d173704 q = 1) : d39 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d173704 q = 1) : d40 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d173704 q = 1) : d41 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d173704 q = 1) : d49 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39127 (p : Pattern) (ha : d89 p = 1) (hb : d173704 p = 1) : d60 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d173704 q = 1) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39126 q ha hb
    | true =>
      simp only [d84, d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d173704 q = 1) : d51 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d173704 q = 1) : d52 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d173704 q = 1) : d53 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d173704 q = 1) : d54 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d173704 q = 1) : d60 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39128 (p : Pattern) (ha : d95 p = 1) (hb : d173704 p = 1) : d175332 p = 1 := by
  have h0 (q : Pattern) (ha : d65 q = 1) (hb : d173704 q = 1) : d65 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d90 q = 1) (hb : d173704 q = 1) : d61 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d90, d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39127 q ha hb
  have h3 (q : Pattern) (ha : d91 q = 1) (hb : d173704 q = 1) : d62 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d91, d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d92 q = 1) (hb : d173704 q = 1) : d63 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92, d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d93 q = 1) (hb : d173704 q = 1) : d64 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93, d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d94 q = 1) (hb : d173704 q = 1) : d175331 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, d175331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94, d175331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d95 q = 1) (hb : d173704 q = 1) : d175332 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, d175332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d95, d175332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39129 (p : Pattern) (ha : d231 p = 1) (hb : d173704 p = 1) : d144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d227 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140 q = 1) (hb : d131097 q = 1) : d140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d228 q = 1) (hb : d173703 q = 1) : d141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d173703, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d228, d173703, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d229 q = 1) (hb : d173704 q = 1) : d142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d173704, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d229, d173704, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d67 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d131097 q = 1) : d26 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d68 q = 1) (hb : d173703 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69 q = 1) (hb : d173704 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d230 q = 1) (hb : d173704 q = 1) : d143 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d230, d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70 q = 1) (hb : d173704 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d231 q = 1) (hb : d173704 q = 1) : d144 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231, d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39130 (p : Pattern) (ha : d237 p = 1) (hb : d173704 p = 1) : d150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39129 q ha hb
    | true =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39124 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d173704 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39124 q ha hb
    | true =>
      simp only [d72, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d173704 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d173704 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d173704 q = 1) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d173704 q = 1) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d236 q = 1) (hb : d173704 q = 1) : d149 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236, d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237 q = 1) (hb : d173704 q = 1) : d150 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237, d150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39131 (p : Pattern) (ha : d243 p = 1) (hb : d173704 p = 1) : d203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d173704 q = 1) : d151 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39130 q ha hb
    | true =>
      simp only [d238, d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d173704 q = 1) : d152 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d173704 q = 1) : d37 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39125 q ha hb
    | true =>
      simp only [d78, d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d173704 q = 1) : d38 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d240 q = 1) (hb : d173704 q = 1) : d153 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241 q = 1) (hb : d173704 q = 1) : d154 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241, d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d242 q = 1) (hb : d173704 q = 1) : d155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242, d155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d243 q = 1) (hb : d173704 q = 1) : d203 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243, d203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39132 (p : Pattern) (ha : d4359 p = 1) (hb : d173704 p = 1) : d4349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d173704 q = 1) : d204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39131 q ha hb
    | true =>
      simp only [d244, d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39126 q ha hb
  have h2 (q : Pattern) (ha : d4355 q = 1) (hb : d173704 q = 1) : d4340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4355, d4340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d173704 q = 1) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39126 q ha hb
    | true =>
      simp only [d84, d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d173704 q = 1) : d51 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d173704 q = 1) : d4341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d4341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4356, d4341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d173704 q = 1) : d4342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d4342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d4342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d173704 q = 1) : d4343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d4343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d4343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d173704 q = 1) : d4349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d4349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d4349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39133 (p : Pattern) (ha : d51652 p = 1) (hb : d173704 p = 1) : d175338 p = 1 := by
  have h0 (q : Pattern) (ha : d51651 q = 1) (hb : d173704 q = 1) : d51651 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4360 q = 1) (hb : d173704 q = 1) : d4350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d4350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4360, d4350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39132 q ha hb
  have h3 (q : Pattern) (ha : d4361 q = 1) (hb : d173704 q = 1) : d4351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d4351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4361, d4351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d4362 q = 1) (hb : d173704 q = 1) : d4352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4362, d4352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d4363 q = 1) (hb : d173704 q = 1) : d4353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4363, d4353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d4364 q = 1) (hb : d173704 q = 1) : d175337 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d175337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4364, d175337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51652 q = 1) (hb : d173704 q = 1) : d175338 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d175338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51652, d175338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39134 (p : Pattern) (ha : d462 p = 1) (hb : d173704 p = 1) : d406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d173704 q = 1) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39126 q ha hb
    | true =>
      simp only [d84, d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d173704 q = 1) : d107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d173704 q = 1) : d108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d173704 q = 1) : d109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d173704 q = 1) : d110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d173704 q = 1) : d406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39135 (p : Pattern) (ha : d5377 p = 1) (hb : d173704 p = 1) : d5355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d173704 q = 1) : d151 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39130 q ha hb
    | true =>
      simp only [d238, d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d173704 q = 1) : d152 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d173704 q = 1) : d4733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d4733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d173704 q = 1) : d4734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d4734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d4734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d173704 q = 1) : d4735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d4735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d4735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d173704 q = 1) : d5355 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d5355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d5355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39136 (p : Pattern) (ha : d16004 p = 1) (hb : d173704 p = 1) : d15966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d413 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320 q = 1) (hb : d131097 q = 1) : d320 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d414 q = 1) (hb : d173703 q = 1) : d321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d173703, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d414, d173703, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d415 q = 1) (hb : d173704 q = 1) : d322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d173704, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d415, d173704, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d227 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d131097 q = 1) : d140 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d228 q = 1) (hb : d173703 q = 1) : d141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d173703, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d228, d173703, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d229 q = 1) (hb : d173704 q = 1) : d142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d173704, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d229, d173704, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d416 q = 1) (hb : d173704 q = 1) : d323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d416, d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12600 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d131097 q = 1) : d9384 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d12601 q = 1) (hb : d173703 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d12601, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12602 q = 1) (hb : d173704 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12602, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d67 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d131097 q = 1) : d26 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d68 q = 1) (hb : d173703 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d68, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69 q = 1) (hb : d173704 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d12603 q = 1) (hb : d173704 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12603, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16004 q = 1) (hb : d173704 q = 1) : d15966 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16004, d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39137 (p : Pattern) (ha : d16010 p = 1) (hb : d173704 p = 1) : d15972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d173704 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39136 q ha hb
    | true =>
      simp only [d16005, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39129 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d173704 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d173704 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39129 q ha hb
    | true =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39124 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d173704 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d173704 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39124 q ha hb
    | true =>
      simp only [d72, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d173704 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d173704 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235 q = 1) (hb : d173704 q = 1) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d235, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16009 q = 1) (hb : d173704 q = 1) : d15971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16009, d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16010 q = 1) (hb : d173704 q = 1) : d15972 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d15972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16010, d15972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39138 (p : Pattern) (ha : d16016 p = 1) (hb : d173704 p = 1) : d15985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d173704 q = 1) : d15973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d15973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39137 q ha hb
    | true =>
      simp only [d16011, d15973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d173704 q = 1) : d15974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d15974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d15974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d173704 q = 1) : d151 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39130 q ha hb
    | true =>
      simp only [d238, d151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d173704 q = 1) : d152 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d173704 q = 1) : d15975 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d15975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d15975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d173704 q = 1) : d15976 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d15976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d15976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d173704 q = 1) : d15977 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d15977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d15977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d173704 q = 1) : d15985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d15985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d15985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39139 (p : Pattern) (ha : d128217 p = 1) (hb : d173704 p = 1) : d128207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d173704 q = 1) : d15986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d15986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39138 q ha hb
    | true =>
      simp only [d16017, d15986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39131 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d173704 q = 1) : d128196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d173704 q = 1) : d5356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39135 q ha hb
    | true =>
      simp only [d5378, d5356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d173704 q = 1) : d5357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d5357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d173704 q = 1) : d128197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d173704 q = 1) : d128205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d173704 q = 1) : d128206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d173704 q = 1) : d128207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d128207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d128207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39140 (p : Pattern) (ha : d128223 p = 1) (hb : d173704 p = 1) : d175345 p = 1 := by
  have h0 (q : Pattern) (ha : d128212 q = 1) (hb : d173704 q = 1) : d128212 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128218 q = 1) (hb : d173704 q = 1) : d128208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d128208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128218, d128208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39139 q ha hb
  have h3 (q : Pattern) (ha : d463 q = 1) (hb : d173704 q = 1) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d463, d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39134 q ha hb
  have h4 (q : Pattern) (ha : d128219 q = 1) (hb : d173704 q = 1) : d128209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d128209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128219, d128209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128220 q = 1) (hb : d173704 q = 1) : d128210 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d128210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128220, d128210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128221 q = 1) (hb : d173704 q = 1) : d128211 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d128211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128221, d128211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128222 q = 1) (hb : d173704 q = 1) : d175344 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d175344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128222, d175344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128223 q = 1) (hb : d173704 q = 1) : d175345 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d175345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128223, d175345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39141 (p : Pattern) (ha : d128229 p = 1) (hb : d173704 p = 1) : d175351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d173704 q = 1) : d175333 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d175333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d175333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39128 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d173704 q = 1) : d175334 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d175334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d175334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d173704 q = 1) : d175335 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d175335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d175335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d173704 q = 1) : d175336 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d175336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d175336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d173704 q = 1) : d175339 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d175339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, d175339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39133 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d173704 q = 1) : d175340 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d175340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, d175340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d173704 q = 1) : d175341 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d175341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, d175341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d173704 q = 1) : d175342 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d175342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, d175342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d173704 q = 1) : d175343 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d175343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, d175343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128224 q = 1) (hb : d173704 q = 1) : d175346 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d175346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128224, d175346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39140 q ha hb
  have h11 (q : Pattern) (ha : d128225 q = 1) (hb : d173704 q = 1) : d175347 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d175347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128225, d175347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128226 q = 1) (hb : d173704 q = 1) : d175348 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d175348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128226, d175348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128227 q = 1) (hb : d173704 q = 1) : d175349 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d175349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128227, d175349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128228 q = 1) (hb : d173704 q = 1) : d175350 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d175350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128228, d175350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128229 q = 1) (hb : d173704 q = 1) : d175351 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d175351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128229, d175351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39142 (p : Pattern) (ha : d683 p = 1) (hb : d173704 p = 1) : d481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39129 q ha hb
    | true =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39124 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d173704 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d682 q = 1) (hb : d173704 q = 1) : d480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d683 q = 1) (hb : d173704 q = 1) : d481 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d683, d481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39143 (p : Pattern) (ha : d730 p = 1) (hb : d173704 p = 1) : d501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d173704 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39142 q ha hb
    | true =>
      simp only [d684, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d173704 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d173704 q = 1) : d488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d173704 q = 1) : d489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d173704 q = 1) : d490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d173704 q = 1) : d501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39144 (p : Pattern) (ha : d736 p = 1) (hb : d173704 p = 1) : d653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d173704 q = 1) : d639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39143 q ha hb
    | true =>
      simp only [d731, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d173704 q = 1) : d640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d173704 q = 1) : d641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d173704 q = 1) : d642 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d173704 q = 1) : d643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d173704 q = 1) : d653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39145 (p : Pattern) (ha : d16162 p = 1) (hb : d173704 p = 1) : d16077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d660 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d544 q = 1) (hb : d131097 q = 1) : d544 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d661 q = 1) (hb : d173703 q = 1) : d545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d173703, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d661, d173703, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d662 q = 1) (hb : d173704 q = 1) : d546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d173704, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d662, d173704, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d131097 q = 1) : d9460 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d16158 q = 1) (hb : d173703 q = 1) : d16073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d173703, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d16158, d173703, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16159 q = 1) (hb : d173704 q = 1) : d16074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d173704, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16159, d173704, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d16160 q = 1) (hb : d173704 q = 1) : d16075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16160, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12859 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d131097 q = 1) : d9470 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d12860 q = 1) (hb : d173703 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d12860, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12861 q = 1) (hb : d173704 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12861, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12600 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d131097 q = 1) : d9384 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d12601 q = 1) (hb : d173703 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d12601, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12602 q = 1) (hb : d173704 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12602, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d16161 q = 1) (hb : d173704 q = 1) : d16076 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16161, d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16161, d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16162 q = 1) (hb : d173704 q = 1) : d16077 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16162, d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39146 (p : Pattern) (ha : d16166 p = 1) (hb : d173704 p = 1) : d16081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9384 q = 1) (hb : d131097 q = 1) : d9384 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12601 q = 1) (hb : d173703 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12601, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12602 q = 1) (hb : d173704 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12602, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d67 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d131097 q = 1) : d26 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d68 q = 1) (hb : d173703 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69 q = 1) (hb : d173704 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d12603 q = 1) (hb : d173704 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12603, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70 q = 1) (hb : d173704 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16166 q = 1) (hb : d173704 q = 1) : d16081 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16166, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39147 (p : Pattern) (ha : d16172 p = 1) (hb : d173704 p = 1) : d16087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d173704 q = 1) : d16078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39145 q ha hb
    | true =>
      simp only [d16163, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39136 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d173704 q = 1) : d16079 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d16079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d16079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d173704 q = 1) : d16080 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d16080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d16080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d173704 q = 1) : d16082 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39136 q ha hb
    | true =>
      simp only [d16167, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39146 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d173704 q = 1) : d16083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d16083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d16083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d173704 q = 1) : d16084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d16084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d16084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d173704 q = 1) : d16085 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d16085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d16085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d173704 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39136 q ha hb
    | true =>
      simp only [d16005, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39129 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d173704 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d173704 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d232 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39129 q ha hb
    | true =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39124 q ha hb
  have h12 (q : Pattern) (ha : d233 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16008 q = 1) (hb : d173704 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16171 q = 1) (hb : d173704 q = 1) : d16086 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d16086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d16086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16172 q = 1) (hb : d173704 q = 1) : d16087 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d16087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16172, d16087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39148 (p : Pattern) (ha : d16176 p = 1) (hb : d173704 p = 1) : d16036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d173704 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39136 q ha hb
    | true =>
      simp only [d16005, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39129 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d173704 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d173704 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39129 q ha hb
    | true =>
      simp only [d232, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39124 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d173704 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d673 q = 1) (hb : d173704 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d673, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16175 q = 1) (hb : d173704 q = 1) : d16035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16175, d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16176 q = 1) (hb : d173704 q = 1) : d16036 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d16036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16176, d16036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39149 (p : Pattern) (ha : d16182 p = 1) (hb : d173704 p = 1) : d16130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d173704 q = 1) : d16088 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d16088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39147 q ha hb
    | true =>
      simp only [d16173, d16088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d173704 q = 1) : d16089 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d16089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d16089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d173704 q = 1) : d16037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39148 q ha hb
    | true =>
      simp only [d16177, d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d173704 q = 1) : d16038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d173704 q = 1) : d16090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d16090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d16090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d173704 q = 1) : d16091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d16091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d16091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d173704 q = 1) : d16092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d16092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d16092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d173704 q = 1) : d16130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d16130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d16130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39150 (p : Pattern) (ha : d16186 p = 1) (hb : d173704 p = 1) : d16051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d173704 q = 1) : d16037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39148 q ha hb
    | true =>
      simp only [d16177, d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d173704 q = 1) : d16038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d173704 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39142 q ha hb
    | true =>
      simp only [d684, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d173704 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d173704 q = 1) : d16039 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d16039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d16039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d173704 q = 1) : d16040 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d16040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d16040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d173704 q = 1) : d16041 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d16041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d16041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d173704 q = 1) : d16051 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d16051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d16051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39151 (p : Pattern) (ha : d16207 p = 1) (hb : d173704 p = 1) : d16135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d173704 q = 1) : d16037 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39148 q ha hb
    | true =>
      simp only [d16177, d16037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d173704 q = 1) : d16038 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d16038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d173704 q = 1) : d16111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d16111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d16111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d173704 q = 1) : d16112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d16112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d16112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d173704 q = 1) : d16113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d16113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d16113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d173704 q = 1) : d16135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d16135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d16135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39152 (p : Pattern) (ha : d128256 p = 1) (hb : d173704 p = 1) : d128246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d173704 q = 1) : d16131 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d16131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39149 q ha hb
    | true =>
      simp only [d16187, d16131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39150 q ha hb
  have h2 (q : Pattern) (ha : d128252 q = 1) (hb : d173704 q = 1) : d128235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128252, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d173704 q = 1) : d16136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d16136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39151 q ha hb
    | true =>
      simp only [d16208, d16136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d173704 q = 1) : d16137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d16137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d16137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d173704 q = 1) : d128236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d173704 q = 1) : d128244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d128244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d128244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d173704 q = 1) : d128245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d128245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d128245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d173704 q = 1) : d128246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d128246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d128246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39153 (p : Pattern) (ha : d128262 p = 1) (hb : d173704 p = 1) : d175353 p = 1 := by
  have h0 (q : Pattern) (ha : d128251 q = 1) (hb : d173704 q = 1) : d128251 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128257 q = 1) (hb : d173704 q = 1) : d128247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d128247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128257, d128247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39152 q ha hb
  have h3 (q : Pattern) (ha : d737 q = 1) (hb : d173704 q = 1) : d654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d737, d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39144 q ha hb
  have h4 (q : Pattern) (ha : d128258 q = 1) (hb : d173704 q = 1) : d128248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d128248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128258, d128248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128259 q = 1) (hb : d173704 q = 1) : d128249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d128249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128259, d128249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128260 q = 1) (hb : d173704 q = 1) : d128250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d128250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128260, d128250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128261 q = 1) (hb : d173704 q = 1) : d175352 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d175352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128261, d175352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128262 q = 1) (hb : d173704 q = 1) : d175353 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d175353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128262, d175353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39154 (p : Pattern) (ha : d128268 p = 1) (hb : d173704 p = 1) : d175359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d173704 q = 1) : d175354 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d175354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d175354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39153 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d173704 q = 1) : d175355 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d175355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d175355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d173704 q = 1) : d175356 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d175356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d175356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d173704 q = 1) : d175357 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d175357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d175357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d173704 q = 1) : d175358 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d175358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d175358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d173704 q = 1) : d175359 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d175359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d175359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39155 (p : Pattern) (ha : d981 p = 1) (hb : d173704 p = 1) : d758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d413 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320 q = 1) (hb : d131097 q = 1) : d320 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d414 q = 1) (hb : d173703 q = 1) : d321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d173703, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d414, d173703, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d415 q = 1) (hb : d173704 q = 1) : d322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d173704, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d415, d173704, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d972 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d131097 q = 1) : d752 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d973 q = 1) (hb : d173703 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d973, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d974 q = 1) (hb : d173704 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d974, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d975 q = 1) (hb : d173704 q = 1) : d755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d975, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d980 q = 1) (hb : d173704 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d980, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d981 q = 1) (hb : d173704 q = 1) : d758 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d981, d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39156 (p : Pattern) (ha : d986 p = 1) (hb : d173704 p = 1) : d762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d752 q = 1) (hb : d131097 q = 1) : d752 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d973 q = 1) (hb : d173703 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d973, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d974 q = 1) (hb : d173704 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d974, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d980 q = 1) (hb : d173704 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d980, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d986 q = 1) (hb : d173704 q = 1) : d762 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d986, d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro39157 (p : Pattern) (ha : d1005 p = 1) (hb : d173704 p = 1) : d773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d173704 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39155 q ha hb
    | true =>
      simp only [d987, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39156 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d173704 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d173704 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d173704 q = 1) : d767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d173704 q = 1) : d772 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d173704 q = 1) : d773 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39158 (p : Pattern) (ha : d1063 p = 1) (hb : d173704 p = 1) : d793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d173704 q = 1) : d774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39157 q ha hb
    | true =>
      simp only [d1006, d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d173704 q = 1) : d775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d173704 q = 1) : d780 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d173704 q = 1) : d781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d173704 q = 1) : d782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d173704 q = 1) : d793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39159 (p : Pattern) (ha : d1069 p = 1) (hb : d173704 p = 1) : d959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d173704 q = 1) : d945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39158 q ha hb
    | true =>
      simp only [d1064, d945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d173704 q = 1) : d946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d173704 q = 1) : d947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d173704 q = 1) : d948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d173704 q = 1) : d949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d173704 q = 1) : d959 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39160 (p : Pattern) (ha : d16362 p = 1) (hb : d173704 p = 1) : d16274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d835 q = 1) (hb : d131097 q = 1) : d835 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d967 q = 1) (hb : d173703 q = 1) : d836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d173703, d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d967, d173703, d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d968 q = 1) (hb : d173704 q = 1) : d837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d173704, d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d968, d173704, d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16357 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9589 q = 1) (hb : d131097 q = 1) : d9589 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d16358 q = 1) (hb : d173703 q = 1) : d16270 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d173703, d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d16358, d173703, d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16359 q = 1) (hb : d173704 q = 1) : d16271 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16359, d173704, d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16359, d173704, d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d16360 q = 1) (hb : d173704 q = 1) : d16272 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16360, d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14645 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9599 q = 1) (hb : d131097 q = 1) : d9599 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14646 q = 1) (hb : d173703 q = 1) : d14529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d173703, d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d14646, d173703, d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14647 q = 1) (hb : d173704 q = 1) : d14530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d173704, d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14647, d173704, d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12859 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d131097 q = 1) : d9470 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d12860 q = 1) (hb : d173703 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d12860, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12861 q = 1) (hb : d173704 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12861, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d16361 q = 1) (hb : d173704 q = 1) : d16273 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16361, d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16361, d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16362 q = 1) (hb : d173704 q = 1) : d16274 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16362, d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39161 (p : Pattern) (ha : d16363 p = 1) (hb : d173704 p = 1) : d16227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d660 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d544 q = 1) (hb : d131097 q = 1) : d544 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d661 q = 1) (hb : d173703 q = 1) : d545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d173703, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d661, d173703, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d662 q = 1) (hb : d173704 q = 1) : d546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d173704, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d662, d173704, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d131097 q = 1) : d9460 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d16158 q = 1) (hb : d173703 q = 1) : d16073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d173703, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d16158, d173703, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16159 q = 1) (hb : d173704 q = 1) : d16074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d173704, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16159, d173704, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d16160 q = 1) (hb : d173704 q = 1) : d16075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16160, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12859 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d131097 q = 1) : d9470 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d12860 q = 1) (hb : d173703 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d12860, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12861 q = 1) (hb : d173704 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12861, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d972 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d131097 q = 1) : d752 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d973 q = 1) (hb : d173703 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d973, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d974 q = 1) (hb : d173704 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d974, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d12862 q = 1) (hb : d173704 q = 1) : d12750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12862, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16363 q = 1) (hb : d173704 q = 1) : d16227 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16363, d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39162 (p : Pattern) (ha : d16367 p = 1) (hb : d173704 p = 1) : d16278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12859 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9470 q = 1) (hb : d131097 q = 1) : d9470 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12860 q = 1) (hb : d173703 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12860, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12861 q = 1) (hb : d173704 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12861, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d972 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d131097 q = 1) : d752 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d973 q = 1) (hb : d173703 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d973, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d974 q = 1) (hb : d173704 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d974, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d12862 q = 1) (hb : d173704 q = 1) : d12750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12862, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d980 q = 1) (hb : d173704 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d980, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16367 q = 1) (hb : d173704 q = 1) : d16278 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16367, d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39163 (p : Pattern) (ha : d16377 p = 1) (hb : d173704 p = 1) : d16284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d173704 q = 1) : d16275 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39160 q ha hb
    | true =>
      simp only [d16364, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39161 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d173704 q = 1) : d16276 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d16276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d16276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d173704 q = 1) : d16277 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d16277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d16277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d173704 q = 1) : d16279 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39161 q ha hb
    | true =>
      simp only [d16368, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39162 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d173704 q = 1) : d16280 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d16280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d16280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d173704 q = 1) : d16281 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d16281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d16281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d173704 q = 1) : d16282 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d16282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d16282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d173704 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39161 q ha hb
    | true =>
      simp only [d16372, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39155 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d173704 q = 1) : d16229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d173704 q = 1) : d16230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d173704 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39155 q ha hb
    | true =>
      simp only [d987, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39156 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d173704 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d173704 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16375 q = 1) (hb : d173704 q = 1) : d16231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16376 q = 1) (hb : d173704 q = 1) : d16283 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d16283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d16283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16377 q = 1) (hb : d173704 q = 1) : d16284 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16377, d16284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16377, d16284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39164 (p : Pattern) (ha : d16381 p = 1) (hb : d173704 p = 1) : d16233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d173704 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39161 q ha hb
    | true =>
      simp only [d16372, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39155 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d173704 q = 1) : d16229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d173704 q = 1) : d16230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d173704 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39155 q ha hb
    | true =>
      simp only [d987, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39156 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d173704 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d173704 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16375 q = 1) (hb : d173704 q = 1) : d16231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d173704 q = 1) : d767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16380 q = 1) (hb : d173704 q = 1) : d16232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d16232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16380, d16232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16381 q = 1) (hb : d173704 q = 1) : d16233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16381, d16233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16381, d16233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39165 (p : Pattern) (ha : d16387 p = 1) (hb : d173704 p = 1) : d16330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16378 q = 1) (hb : d173704 q = 1) : d16285 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16378, d16285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39163 q ha hb
    | true =>
      simp only [d16378, d16285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16379 q = 1) (hb : d173704 q = 1) : d16286 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16379, d16286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16379, d16286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16382 q = 1) (hb : d173704 q = 1) : d16234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d16234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39164 q ha hb
    | true =>
      simp only [d16382, d16234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16383 q = 1) (hb : d173704 q = 1) : d16235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d16235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d16235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16384 q = 1) (hb : d173704 q = 1) : d16287 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16384, d16287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16384, d16287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16385 q = 1) (hb : d173704 q = 1) : d16288 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16385, d16288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16385, d16288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16386 q = 1) (hb : d173704 q = 1) : d16289 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16386, d16289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16386, d16289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16387 q = 1) (hb : d173704 q = 1) : d16330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16387, d16330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16387, d16330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39166 (p : Pattern) (ha : d16391 p = 1) (hb : d173704 p = 1) : d16248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d173704 q = 1) : d16234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d16234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39164 q ha hb
    | true =>
      simp only [d16382, d16234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d173704 q = 1) : d16235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d16235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d16235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d173704 q = 1) : d774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39157 q ha hb
    | true =>
      simp only [d1006, d774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d173704 q = 1) : d775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16388 q = 1) (hb : d173704 q = 1) : d16236 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16388, d16236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16388, d16236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16389 q = 1) (hb : d173704 q = 1) : d16237 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16389, d16237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16389, d16237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16390 q = 1) (hb : d173704 q = 1) : d16238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16390, d16238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16390, d16238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16391 q = 1) (hb : d173704 q = 1) : d16248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16391, d16248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16391, d16248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39167 (p : Pattern) (ha : d16417 p = 1) (hb : d173704 p = 1) : d16335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d173704 q = 1) : d16234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d16234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39164 q ha hb
    | true =>
      simp only [d16382, d16234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d173704 q = 1) : d16235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d16235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d16235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16414 q = 1) (hb : d173704 q = 1) : d16311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16414, d16311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16414, d16311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16415 q = 1) (hb : d173704 q = 1) : d16312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16415, d16312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16415, d16312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16416 q = 1) (hb : d173704 q = 1) : d16313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16416, d16313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16416, d16313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16417 q = 1) (hb : d173704 q = 1) : d16335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16417, d16335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16417, d16335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39168 (p : Pattern) (ha : d128296 p = 1) (hb : d173704 p = 1) : d128286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16392 q = 1) (hb : d173704 q = 1) : d16331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16392, d16331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39165 q ha hb
    | true =>
      simp only [d16392, d16331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39166 q ha hb
  have h2 (q : Pattern) (ha : d128292 q = 1) (hb : d173704 q = 1) : d128275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128292, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16418 q = 1) (hb : d173704 q = 1) : d16336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16418, d16336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39167 q ha hb
    | true =>
      simp only [d16418, d16336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16419 q = 1) (hb : d173704 q = 1) : d16337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16419, d16337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16419, d16337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d173704 q = 1) : d128276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128293, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d173704 q = 1) : d128284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d128284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d128284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d173704 q = 1) : d128285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d128285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d128285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d173704 q = 1) : d128286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d128286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d128286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39169 (p : Pattern) (ha : d128302 p = 1) (hb : d173704 p = 1) : d175362 p = 1 := by
  have h0 (q : Pattern) (ha : d128291 q = 1) (hb : d173704 q = 1) : d128291 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128297 q = 1) (hb : d173704 q = 1) : d128287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d128287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128297, d128287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39168 q ha hb
  have h3 (q : Pattern) (ha : d1070 q = 1) (hb : d173704 q = 1) : d960 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1070, d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39159 q ha hb
  have h4 (q : Pattern) (ha : d128298 q = 1) (hb : d173704 q = 1) : d128288 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d128288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128298, d128288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128299 q = 1) (hb : d173704 q = 1) : d128289 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d128289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128299, d128289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128300 q = 1) (hb : d173704 q = 1) : d128290 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d128290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128300, d128290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128301 q = 1) (hb : d173704 q = 1) : d175361 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d175361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128301, d175361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128302 q = 1) (hb : d173704 q = 1) : d175362 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d175362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128302, d175362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39170 (p : Pattern) (ha : d128308 p = 1) (hb : d173704 p = 1) : d175368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d173704 q = 1) : d175363 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d175363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d175363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39169 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d173704 q = 1) : d175364 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d175364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d175364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d173704 q = 1) : d175365 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d175365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d175365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d173704 q = 1) : d175366 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d175366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d175366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d173704 q = 1) : d175367 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d175367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d175367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d173704 q = 1) : d175368 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d175368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d175368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39171 (p : Pattern) (ha : d15042 p = 1) (hb : d173704 p = 1) : d14778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1392 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1122 q = 1) (hb : d131097 q = 1) : d1122 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1393 q = 1) (hb : d173703 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1393, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1394 q = 1) (hb : d173704 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1394, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1400 q = 1) (hb : d173704 q = 1) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1400, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15020 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9846 q = 1) (hb : d131097 q = 1) : d9846 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15021 q = 1) (hb : d173703 q = 1) : d14770 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d173703, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15021, d173703, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15022 q = 1) (hb : d173704 q = 1) : d14771 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d173704, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15022, d173704, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d15023 q = 1) (hb : d173704 q = 1) : d14772 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15023, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15042 q = 1) (hb : d173704 q = 1) : d14778 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15042, d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15042, d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39172 (p : Pattern) (ha : d16672 p = 1) (hb : d173704 p = 1) : d16443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1111 q = 1) (hb : d131097 q = 1) : d1111 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1387 q = 1) (hb : d173703 q = 1) : d1112 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d173703, d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1387, d173703, d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1388 q = 1) (hb : d173704 q = 1) : d1113 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d173704, d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1388, d173704, d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1392 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d131097 q = 1) : d1122 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1393 q = 1) (hb : d173703 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1393, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1394 q = 1) (hb : d173704 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1394, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1395 q = 1) (hb : d173704 q = 1) : d1125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1395, d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15005 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9802 q = 1) (hb : d131097 q = 1) : d9802 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15006 q = 1) (hb : d173703 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d15006, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15007 q = 1) (hb : d173704 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15007, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15008 q = 1) (hb : d173704 q = 1) : d14765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15008, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16672 q = 1) (hb : d173704 q = 1) : d16443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16672, d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16672, d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro39173 (p : Pattern) (ha : d16698 p = 1) (hb : d173704 p = 1) : d16460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16693 q = 1) (hb : d173704 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
    | true =>
      simp only [d16693, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39171 q ha hb
  have h2 (q : Pattern) (ha : d16694 q = 1) (hb : d173704 q = 1) : d16452 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16695 q = 1) (hb : d173704 q = 1) : d16453 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16696 q = 1) (hb : d173704 q = 1) : d16454 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16696, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16697 q = 1) (hb : d173704 q = 1) : d16459 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d16459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16697, d16459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16698 q = 1) (hb : d173704 q = 1) : d16460 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16698, d16460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16698, d16460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39174 (p : Pattern) (ha : d16765 p = 1) (hb : d173704 p = 1) : d16480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16699 q = 1) (hb : d173704 q = 1) : d16461 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d16461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39173 q ha hb
    | true =>
      simp only [d16699, d16461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16700 q = 1) (hb : d173704 q = 1) : d16462 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d16462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d16462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16762 q = 1) (hb : d173704 q = 1) : d16467 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16762, d16467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16762, d16467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16763 q = 1) (hb : d173704 q = 1) : d16468 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16763, d16468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16763, d16468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16764 q = 1) (hb : d173704 q = 1) : d16469 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16764, d16469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16764, d16469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16765 q = 1) (hb : d173704 q = 1) : d16480 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16765, d16480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16765, d16480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39175 (p : Pattern) (ha : d16771 p = 1) (hb : d173704 p = 1) : d16643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16766 q = 1) (hb : d173704 q = 1) : d16629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16766, d16629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39174 q ha hb
    | true =>
      simp only [d16766, d16629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16767 q = 1) (hb : d173704 q = 1) : d16630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16767, d16630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16767, d16630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16768 q = 1) (hb : d173704 q = 1) : d16631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16768, d16631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16768, d16631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16769 q = 1) (hb : d173704 q = 1) : d16632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16769, d16632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16769, d16632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16770 q = 1) (hb : d173704 q = 1) : d16633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16770, d16633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16770, d16633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16771 q = 1) (hb : d173704 q = 1) : d16643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16771, d16643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16771, d16643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39176 (p : Pattern) (ha : d15024 p = 1) (hb : d173704 p = 1) : d14773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5019 q = 1) (hb : d131097 q = 1) : d5019 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6352 q = 1) (hb : d173703 q = 1) : d5020 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d173703, d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6352, d173703, d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6353 q = 1) (hb : d173704 q = 1) : d5021 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d173704, d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6353, d173704, d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6354 q = 1) (hb : d173704 q = 1) : d5022 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6354, d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15020 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9846 q = 1) (hb : d131097 q = 1) : d9846 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15021 q = 1) (hb : d173703 q = 1) : d14770 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d173703, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15021, d173703, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15022 q = 1) (hb : d173704 q = 1) : d14771 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d173704, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15022, d173704, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d15023 q = 1) (hb : d173704 q = 1) : d14772 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15023, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15024 q = 1) (hb : d173704 q = 1) : d14773 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15024, d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15024, d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39177 (p : Pattern) (ha : d16655 p = 1) (hb : d173704 p = 1) : d16511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1377 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1211 q = 1) (hb : d131097 q = 1) : d1211 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1378 q = 1) (hb : d173703 q = 1) : d1212 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d173703, d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1378, d173703, d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1379 q = 1) (hb : d173704 q = 1) : d1213 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d173704, d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1379, d173704, d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16650 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9755 q = 1) (hb : d131097 q = 1) : d9755 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d16651 q = 1) (hb : d173703 q = 1) : d16507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16651, d173703, d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d16651, d173703, d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16652 q = 1) (hb : d173704 q = 1) : d16508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16652, d173704, d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16652, d173704, d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d16653 q = 1) (hb : d173704 q = 1) : d16509 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16653, d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16653, d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14988 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9765 q = 1) (hb : d131097 q = 1) : d9765 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14989 q = 1) (hb : d173703 q = 1) : d14836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14989, d173703, d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d14989, d173703, d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14990 q = 1) (hb : d173704 q = 1) : d14837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14990, d173704, d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14990, d173704, d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14995 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9780 q = 1) (hb : d131097 q = 1) : d9780 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d14996 q = 1) (hb : d173703 q = 1) : d14758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d173703, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d14996, d173703, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14997 q = 1) (hb : d173704 q = 1) : d14759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d173704, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14997, d173704, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d16654 q = 1) (hb : d173704 q = 1) : d16510 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16654, d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16654, d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16655 q = 1) (hb : d173704 q = 1) : d16511 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16655, d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16655, d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39178 (p : Pattern) (ha : d16662 p = 1) (hb : d173704 p = 1) : d16442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1101 q = 1) (hb : d131097 q = 1) : d1101 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1382 q = 1) (hb : d173703 q = 1) : d1102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d173703, d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1382, d173703, d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1383 q = 1) (hb : d173704 q = 1) : d1103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d173704, d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1383, d173704, d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16657 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9791 q = 1) (hb : d131097 q = 1) : d9791 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d16658 q = 1) (hb : d173703 q = 1) : d16438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16658, d173703, d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d16658, d173703, d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16659 q = 1) (hb : d173704 q = 1) : d16439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16659, d173704, d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16659, d173704, d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d16660 q = 1) (hb : d173704 q = 1) : d16440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16660, d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16660, d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14995 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9780 q = 1) (hb : d131097 q = 1) : d9780 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14996 q = 1) (hb : d173703 q = 1) : d14758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d173703, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d14996, d173703, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14997 q = 1) (hb : d173704 q = 1) : d14759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d173704, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14997, d173704, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15005 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9802 q = 1) (hb : d131097 q = 1) : d9802 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15006 q = 1) (hb : d173703 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d15006, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15007 q = 1) (hb : d173704 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15007, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d16661 q = 1) (hb : d173704 q = 1) : d16441 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16661, d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16661, d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16662 q = 1) (hb : d173704 q = 1) : d16442 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16662, d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16662, d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39179 (p : Pattern) (ha : d16667 p = 1) (hb : d173704 p = 1) : d16516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13161 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9816 q = 1) (hb : d131097 q = 1) : d9816 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13162 q = 1) (hb : d173703 q = 1) : d13022 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d173703, d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13162, d173703, d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13163 q = 1) (hb : d173704 q = 1) : d13023 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d173704, d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13163, d173704, d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15005 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9802 q = 1) (hb : d131097 q = 1) : d9802 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15006 q = 1) (hb : d173703 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15006, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15007 q = 1) (hb : d173704 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15007, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d16666 q = 1) (hb : d173704 q = 1) : d16515 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16666, d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16666, d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15008 q = 1) (hb : d173704 q = 1) : d14765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15008, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16667 q = 1) (hb : d173704 q = 1) : d16516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16667, d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16667, d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39180 (p : Pattern) (ha : d16681 p = 1) (hb : d173704 p = 1) : d16522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d173704 q = 1) : d16512 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39177 q ha hb
    | true =>
      simp only [d16663, d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39178 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d173704 q = 1) : d16513 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d16513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d16513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d173704 q = 1) : d16514 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d16514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d16514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d173704 q = 1) : d16517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39178 q ha hb
    | true =>
      simp only [d16668, d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39179 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d173704 q = 1) : d16518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d16518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d16518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d173704 q = 1) : d16519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d16519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d16519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d173704 q = 1) : d16520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d16520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d16520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d173704 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39178 q ha hb
    | true =>
      simp only [d16673, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d173704 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d173704 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16676 q = 1) (hb : d173704 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
    | true =>
      simp only [d16676, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39176 q ha hb
  have h12 (q : Pattern) (ha : d16677 q = 1) (hb : d173704 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16678 q = 1) (hb : d173704 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16679 q = 1) (hb : d173704 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16680 q = 1) (hb : d173704 q = 1) : d16521 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d16521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d16521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16681 q = 1) (hb : d173704 q = 1) : d16522 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16681, d16522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16681, d16522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39181 (p : Pattern) (ha : d16686 p = 1) (hb : d173704 p = 1) : d16527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d173704 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39178 q ha hb
    | true =>
      simp only [d16673, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d173704 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d173704 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d173704 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
    | true =>
      simp only [d16676, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39176 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d173704 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d173704 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d173704 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16684 q = 1) (hb : d173704 q = 1) : d16525 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d16525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16684, d16525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16685 q = 1) (hb : d173704 q = 1) : d16526 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d16526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16685, d16526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16686 q = 1) (hb : d173704 q = 1) : d16527 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16686, d16527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16686, d16527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39182 (p : Pattern) (ha : d16692 p = 1) (hb : d173704 p = 1) : d16603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16682 q = 1) (hb : d173704 q = 1) : d16523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16682, d16523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39180 q ha hb
    | true =>
      simp only [d16682, d16523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16683 q = 1) (hb : d173704 q = 1) : d16524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16683, d16524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16683, d16524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16687 q = 1) (hb : d173704 q = 1) : d16528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d16528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39181 q ha hb
    | true =>
      simp only [d16687, d16528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16688 q = 1) (hb : d173704 q = 1) : d16529 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d16529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d16529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16689 q = 1) (hb : d173704 q = 1) : d16530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16689, d16530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16689, d16530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16690 q = 1) (hb : d173704 q = 1) : d16531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16690, d16531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16690, d16531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16691 q = 1) (hb : d173704 q = 1) : d16532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16691, d16532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16691, d16532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16692 q = 1) (hb : d173704 q = 1) : d16603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16692, d16603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16692, d16603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39183 (p : Pattern) (ha : d16704 p = 1) (hb : d173704 p = 1) : d16604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16687 q = 1) (hb : d173704 q = 1) : d16528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d16528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39181 q ha hb
    | true =>
      simp only [d16687, d16528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16688 q = 1) (hb : d173704 q = 1) : d16529 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d16529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d16529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d173704 q = 1) : d16461 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d16461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39173 q ha hb
    | true =>
      simp only [d16699, d16461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d173704 q = 1) : d16462 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d16462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d16462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16701 q = 1) (hb : d173704 q = 1) : d16534 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16701, d16534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16701, d16534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16702 q = 1) (hb : d173704 q = 1) : d16535 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16702, d16535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16702, d16535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16703 q = 1) (hb : d173704 q = 1) : d16536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16703, d16536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16703, d16536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16704 q = 1) (hb : d173704 q = 1) : d16604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16704, d16604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16704, d16604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39184 (p : Pattern) (ha : d13190 p = 1) (hb : d173704 p = 1) : d12961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1392 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1122 q = 1) (hb : d131097 q = 1) : d1122 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1393 q = 1) (hb : d173703 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1393, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1394 q = 1) (hb : d173704 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1394, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1400 q = 1) (hb : d173704 q = 1) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1400, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13190 q = 1) (hb : d173704 q = 1) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13190, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro39185 (p : Pattern) (ha : d16748 p = 1) (hb : d173704 p = 1) : d16579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d173704 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39178 q ha hb
    | true =>
      simp only [d16673, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d173704 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d173704 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d173704 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
    | true =>
      simp only [d16676, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39176 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d173704 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d173704 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d173704 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16743 q = 1) (hb : d173704 q = 1) : d16574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39172 q ha hb
    | true =>
      simp only [d16743, d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39184 q ha hb
  have h9 (q : Pattern) (ha : d16744 q = 1) (hb : d173704 q = 1) : d16575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d16575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d16575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16745 q = 1) (hb : d173704 q = 1) : d16576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d16576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d16576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16746 q = 1) (hb : d173704 q = 1) : d16577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d16577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16746, d16577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16747 q = 1) (hb : d173704 q = 1) : d16578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d16578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16747, d16578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16748 q = 1) (hb : d173704 q = 1) : d16579 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16748, d16579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16748, d16579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39186 (p : Pattern) (ha : d16754 p = 1) (hb : d173704 p = 1) : d16610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16749 q = 1) (hb : d173704 q = 1) : d16580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16749, d16580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39185 q ha hb
    | true =>
      simp only [d16749, d16580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16750 q = 1) (hb : d173704 q = 1) : d16581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16750, d16581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16750, d16581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16751 q = 1) (hb : d173704 q = 1) : d16582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16751, d16582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16751, d16582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16752 q = 1) (hb : d173704 q = 1) : d16583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16752, d16583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16752, d16583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16753 q = 1) (hb : d173704 q = 1) : d16584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16753, d16584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16753, d16584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16754 q = 1) (hb : d173704 q = 1) : d16610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16754, d16610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16754, d16610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39187 (p : Pattern) (ha : d128337 p = 1) (hb : d173704 p = 1) : d128327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16705 q = 1) (hb : d173704 q = 1) : d16605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16705, d16605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39182 q ha hb
    | true =>
      simp only [d16705, d16605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39183 q ha hb
  have h2 (q : Pattern) (ha : d128333 q = 1) (hb : d173704 q = 1) : d128316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128333, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16755 q = 1) (hb : d173704 q = 1) : d16611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16755, d16611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39186 q ha hb
    | true =>
      simp only [d16755, d16611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16756 q = 1) (hb : d173704 q = 1) : d16612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16756, d16612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16756, d16612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d173704 q = 1) : d128317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128334, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d173704 q = 1) : d128325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d128325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d128325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d173704 q = 1) : d128326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d128326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d128326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d173704 q = 1) : d128327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d128327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d128327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39188 (p : Pattern) (ha : d128343 p = 1) (hb : d173704 p = 1) : d175372 p = 1 := by
  have h0 (q : Pattern) (ha : d128332 q = 1) (hb : d173704 q = 1) : d128332 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128338 q = 1) (hb : d173704 q = 1) : d128328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d128328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128338, d128328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39187 q ha hb
  have h3 (q : Pattern) (ha : d16772 q = 1) (hb : d173704 q = 1) : d16644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16772, d16644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16772, d16644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39175 q ha hb
  have h4 (q : Pattern) (ha : d128339 q = 1) (hb : d173704 q = 1) : d128329 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d128329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128339, d128329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128340 q = 1) (hb : d173704 q = 1) : d128330 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d128330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128340, d128330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128341 q = 1) (hb : d173704 q = 1) : d128331 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d128331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128341, d128331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128342 q = 1) (hb : d173704 q = 1) : d175371 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d175371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128342, d175371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128343 q = 1) (hb : d173704 q = 1) : d175372 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d175372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128343, d175372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39189 (p : Pattern) (ha : d128349 p = 1) (hb : d173704 p = 1) : d175378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d173704 q = 1) : d175373 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d175373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d175373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39188 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d173704 q = 1) : d175374 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d175374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d175374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d173704 q = 1) : d175375 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d175375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d175375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d173704 q = 1) : d175376 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d175376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d175376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d173704 q = 1) : d175377 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d175377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d175377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d173704 q = 1) : d175378 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d175378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d175378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39190 (p : Pattern) (ha : d15435 p = 1) (hb : d173704 p = 1) : d15171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1869 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1583 q = 1) (hb : d131097 q = 1) : d1583 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1870 q = 1) (hb : d173703 q = 1) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d173703, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1870, d173703, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1871 q = 1) (hb : d173704 q = 1) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d173704, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1871, d173704, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1877 q = 1) (hb : d173704 q = 1) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1877, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15413 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10137 q = 1) (hb : d131097 q = 1) : d10137 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15414 q = 1) (hb : d173703 q = 1) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d173703, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15414, d173703, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15415 q = 1) (hb : d173704 q = 1) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d173704, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15415, d173704, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d15416 q = 1) (hb : d173704 q = 1) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15416, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15435 q = 1) (hb : d173704 q = 1) : d15171 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15435, d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39191 (p : Pattern) (ha : d17032 p = 1) (hb : d173704 p = 1) : d16795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1863 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1571 q = 1) (hb : d131097 q = 1) : d1571 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1864 q = 1) (hb : d173703 q = 1) : d1572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d173703, d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1864, d173703, d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1865 q = 1) (hb : d173704 q = 1) : d1573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d173704, d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1865, d173704, d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17028 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10117 q = 1) (hb : d131097 q = 1) : d10117 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17029 q = 1) (hb : d173703 q = 1) : d16792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d173703, d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17029, d173703, d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17030 q = 1) (hb : d173704 q = 1) : d16793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17030, d173704, d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17030, d173704, d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d17031 q = 1) (hb : d173704 q = 1) : d16794 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17031, d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15398 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10087 q = 1) (hb : d131097 q = 1) : d10087 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15399 q = 1) (hb : d173703 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d15399, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15400 q = 1) (hb : d173704 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15400, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15401 q = 1) (hb : d173704 q = 1) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15401, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17032 q = 1) (hb : d173704 q = 1) : d16795 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17032, d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro39192 (p : Pattern) (ha : d17058 p = 1) (hb : d173704 p = 1) : d16812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17053 q = 1) (hb : d173704 q = 1) : d16803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
    | true =>
      simp only [d17053, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39190 q ha hb
  have h2 (q : Pattern) (ha : d17054 q = 1) (hb : d173704 q = 1) : d16804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17055 q = 1) (hb : d173704 q = 1) : d16805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17056 q = 1) (hb : d173704 q = 1) : d16806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17056, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17057 q = 1) (hb : d173704 q = 1) : d16811 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d16811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17057, d16811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17058 q = 1) (hb : d173704 q = 1) : d16812 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17058, d16812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17058, d16812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39193 (p : Pattern) (ha : d17130 p = 1) (hb : d173704 p = 1) : d16832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17059 q = 1) (hb : d173704 q = 1) : d16813 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d16813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39192 q ha hb
    | true =>
      simp only [d17059, d16813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17060 q = 1) (hb : d173704 q = 1) : d16814 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d16814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d16814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17127 q = 1) (hb : d173704 q = 1) : d16819 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17127, d16819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17127, d16819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17128 q = 1) (hb : d173704 q = 1) : d16820 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17128, d16820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17128, d16820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17129 q = 1) (hb : d173704 q = 1) : d16821 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17129, d16821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17129, d16821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17130 q = 1) (hb : d173704 q = 1) : d16832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17130, d16832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17130, d16832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39194 (p : Pattern) (ha : d17136 p = 1) (hb : d173704 p = 1) : d16998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17131 q = 1) (hb : d173704 q = 1) : d16984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17131, d16984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39193 q ha hb
    | true =>
      simp only [d17131, d16984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17132 q = 1) (hb : d173704 q = 1) : d16985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17132, d16985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17132, d16985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17133 q = 1) (hb : d173704 q = 1) : d16986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17133, d16986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17133, d16986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17134 q = 1) (hb : d173704 q = 1) : d16987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17134, d16987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17134, d16987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17135 q = 1) (hb : d173704 q = 1) : d16988 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17135, d16988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17135, d16988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17136 q = 1) (hb : d173704 q = 1) : d16998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17136, d16998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17136, d16998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39195 (p : Pattern) (ha : d15417 p = 1) (hb : d173704 p = 1) : d15166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6497 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5135 q = 1) (hb : d131097 q = 1) : d5135 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6498 q = 1) (hb : d173703 q = 1) : d5136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d173703, d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6498, d173703, d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6499 q = 1) (hb : d173704 q = 1) : d5137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d173704, d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6499, d173704, d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6500 q = 1) (hb : d173704 q = 1) : d5138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6500, d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15413 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10137 q = 1) (hb : d131097 q = 1) : d10137 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15414 q = 1) (hb : d173703 q = 1) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d173703, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15414, d173703, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15415 q = 1) (hb : d173704 q = 1) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d173704, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15415, d173704, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d15416 q = 1) (hb : d173704 q = 1) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15416, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15417 q = 1) (hb : d173704 q = 1) : d15166 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15417, d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39196 (p : Pattern) (ha : d17010 p = 1) (hb : d173704 p = 1) : d16863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1666 q = 1) (hb : d131097 q = 1) : d1666 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1855 q = 1) (hb : d173703 q = 1) : d1667 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d173703, d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1855, d173703, d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1856 q = 1) (hb : d173704 q = 1) : d1668 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d173704, d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1856, d173704, d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17005 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d131097 q = 1) : d10038 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17006 q = 1) (hb : d173703 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d173703, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17006, d173703, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17007 q = 1) (hb : d173704 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d173704, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17007, d173704, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d17008 q = 1) (hb : d173704 q = 1) : d16861 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17008, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15381 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10048 q = 1) (hb : d131097 q = 1) : d10048 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15382 q = 1) (hb : d173703 q = 1) : d15229 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d173703, d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d15382, d173703, d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15383 q = 1) (hb : d173704 q = 1) : d15230 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d173704, d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15383, d173704, d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15388 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10065 q = 1) (hb : d131097 q = 1) : d10065 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15389 q = 1) (hb : d173703 q = 1) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d173703, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d15389, d173703, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15390 q = 1) (hb : d173704 q = 1) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d173704, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15390, d173704, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d17009 q = 1) (hb : d173704 q = 1) : d16862 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17009, d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17009, d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17010 q = 1) (hb : d173704 q = 1) : d16863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17010, d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17010, d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39197 (p : Pattern) (ha : d17017 p = 1) (hb : d173704 p = 1) : d16791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1858 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1556 q = 1) (hb : d131097 q = 1) : d1556 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1859 q = 1) (hb : d173703 q = 1) : d1557 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d173703, d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1859, d173703, d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1860 q = 1) (hb : d173704 q = 1) : d1558 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d173704, d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1860, d173704, d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17012 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10076 q = 1) (hb : d131097 q = 1) : d10076 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17013 q = 1) (hb : d173703 q = 1) : d16787 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17013, d173703, d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17013, d173703, d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17014 q = 1) (hb : d173704 q = 1) : d16788 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17014, d173704, d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17014, d173704, d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d17015 q = 1) (hb : d173704 q = 1) : d16789 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17015, d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17015, d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15388 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10065 q = 1) (hb : d131097 q = 1) : d10065 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15389 q = 1) (hb : d173703 q = 1) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d173703, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d15389, d173703, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15390 q = 1) (hb : d173704 q = 1) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d173704, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15390, d173704, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15398 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10087 q = 1) (hb : d131097 q = 1) : d10087 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15399 q = 1) (hb : d173703 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d15399, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15400 q = 1) (hb : d173704 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15400, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d17016 q = 1) (hb : d173704 q = 1) : d16790 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17016, d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17016, d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17017 q = 1) (hb : d173704 q = 1) : d16791 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17017, d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17017, d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39198 (p : Pattern) (ha : d17022 p = 1) (hb : d173704 p = 1) : d16868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10101 q = 1) (hb : d131097 q = 1) : d10101 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13488 q = 1) (hb : d173703 q = 1) : d13348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d173703, d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13488, d173703, d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13489 q = 1) (hb : d173704 q = 1) : d13349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d173704, d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13489, d173704, d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15398 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10087 q = 1) (hb : d131097 q = 1) : d10087 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15399 q = 1) (hb : d173703 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15399, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15400 q = 1) (hb : d173704 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15400, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d17021 q = 1) (hb : d173704 q = 1) : d16867 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17021, d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17021, d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15401 q = 1) (hb : d173704 q = 1) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15401, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17022 q = 1) (hb : d173704 q = 1) : d16868 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17022, d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17022, d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39199 (p : Pattern) (ha : d17041 p = 1) (hb : d173704 p = 1) : d16874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d173704 q = 1) : d16864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39196 q ha hb
    | true =>
      simp only [d17018, d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39197 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d173704 q = 1) : d16865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d16865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d16865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d173704 q = 1) : d16866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d16866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d16866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d173704 q = 1) : d16869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39197 q ha hb
    | true =>
      simp only [d17023, d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39198 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d173704 q = 1) : d16870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d16870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d16870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d173704 q = 1) : d16871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d16871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d16871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d173704 q = 1) : d16872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d16872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d16872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d173704 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39197 q ha hb
    | true =>
      simp only [d17033, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d173704 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d173704 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17036 q = 1) (hb : d173704 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
    | true =>
      simp only [d17036, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39195 q ha hb
  have h12 (q : Pattern) (ha : d17037 q = 1) (hb : d173704 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17038 q = 1) (hb : d173704 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17039 q = 1) (hb : d173704 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17040 q = 1) (hb : d173704 q = 1) : d16873 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d16873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d16873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17041 q = 1) (hb : d173704 q = 1) : d16874 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17041, d16874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17041, d16874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39200 (p : Pattern) (ha : d17046 p = 1) (hb : d173704 p = 1) : d16879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d173704 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39197 q ha hb
    | true =>
      simp only [d17033, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d173704 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d173704 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d173704 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
    | true =>
      simp only [d17036, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39195 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d173704 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d173704 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d173704 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17044 q = 1) (hb : d173704 q = 1) : d16877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d16877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17044, d16877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17045 q = 1) (hb : d173704 q = 1) : d16878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d16878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17045, d16878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17046 q = 1) (hb : d173704 q = 1) : d16879 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17046, d16879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17046, d16879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39201 (p : Pattern) (ha : d17052 p = 1) (hb : d173704 p = 1) : d16958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17042 q = 1) (hb : d173704 q = 1) : d16875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17042, d16875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39199 q ha hb
    | true =>
      simp only [d17042, d16875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17043 q = 1) (hb : d173704 q = 1) : d16876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17043, d16876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17043, d16876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17047 q = 1) (hb : d173704 q = 1) : d16880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d16880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39200 q ha hb
    | true =>
      simp only [d17047, d16880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17048 q = 1) (hb : d173704 q = 1) : d16881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d16881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d16881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17049 q = 1) (hb : d173704 q = 1) : d16882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17049, d16882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17049, d16882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17050 q = 1) (hb : d173704 q = 1) : d16883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17050, d16883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17050, d16883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17051 q = 1) (hb : d173704 q = 1) : d16884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17051, d16884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17051, d16884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17052 q = 1) (hb : d173704 q = 1) : d16958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17052, d16958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17052, d16958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39202 (p : Pattern) (ha : d17064 p = 1) (hb : d173704 p = 1) : d16959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17047 q = 1) (hb : d173704 q = 1) : d16880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d16880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39200 q ha hb
    | true =>
      simp only [d17047, d16880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17048 q = 1) (hb : d173704 q = 1) : d16881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d16881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d16881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d173704 q = 1) : d16813 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d16813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39192 q ha hb
    | true =>
      simp only [d17059, d16813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d173704 q = 1) : d16814 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d16814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d16814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17061 q = 1) (hb : d173704 q = 1) : d16886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17061, d16886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17061, d16886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17062 q = 1) (hb : d173704 q = 1) : d16887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17062, d16887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17062, d16887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17063 q = 1) (hb : d173704 q = 1) : d16888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17063, d16888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17063, d16888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17064 q = 1) (hb : d173704 q = 1) : d16959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17064, d16959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17064, d16959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39203 (p : Pattern) (ha : d13516 p = 1) (hb : d173704 p = 1) : d13287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1869 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1583 q = 1) (hb : d131097 q = 1) : d1583 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1870 q = 1) (hb : d173703 q = 1) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d173703, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1870, d173703, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1871 q = 1) (hb : d173704 q = 1) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d173704, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1871, d173704, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1877 q = 1) (hb : d173704 q = 1) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1877, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13516 q = 1) (hb : d173704 q = 1) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13516, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro39204 (p : Pattern) (ha : d17113 p = 1) (hb : d173704 p = 1) : d16934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d173704 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39197 q ha hb
    | true =>
      simp only [d17033, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d173704 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d173704 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d173704 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
    | true =>
      simp only [d17036, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39195 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d173704 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d173704 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d173704 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17108 q = 1) (hb : d173704 q = 1) : d16929 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39191 q ha hb
    | true =>
      simp only [d17108, d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39203 q ha hb
  have h9 (q : Pattern) (ha : d17109 q = 1) (hb : d173704 q = 1) : d16930 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d16930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d16930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17110 q = 1) (hb : d173704 q = 1) : d16931 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d16931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d16931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17111 q = 1) (hb : d173704 q = 1) : d16932 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d16932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17111, d16932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17112 q = 1) (hb : d173704 q = 1) : d16933 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d16933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17112, d16933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17113 q = 1) (hb : d173704 q = 1) : d16934 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17113, d16934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17113, d16934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39205 (p : Pattern) (ha : d17119 p = 1) (hb : d173704 p = 1) : d16965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17114 q = 1) (hb : d173704 q = 1) : d16935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17114, d16935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39204 q ha hb
    | true =>
      simp only [d17114, d16935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17115 q = 1) (hb : d173704 q = 1) : d16936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17115, d16936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17115, d16936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17116 q = 1) (hb : d173704 q = 1) : d16937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17116, d16937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17116, d16937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17117 q = 1) (hb : d173704 q = 1) : d16938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17117, d16938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17117, d16938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17118 q = 1) (hb : d173704 q = 1) : d16939 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17118, d16939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17118, d16939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17119 q = 1) (hb : d173704 q = 1) : d16965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17119, d16965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17119, d16965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39206 (p : Pattern) (ha : d128379 p = 1) (hb : d173704 p = 1) : d128369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17065 q = 1) (hb : d173704 q = 1) : d16960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17065, d16960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39201 q ha hb
    | true =>
      simp only [d17065, d16960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39202 q ha hb
  have h2 (q : Pattern) (ha : d128375 q = 1) (hb : d173704 q = 1) : d128358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128375, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17120 q = 1) (hb : d173704 q = 1) : d16966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17120, d16966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39205 q ha hb
    | true =>
      simp only [d17120, d16966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17121 q = 1) (hb : d173704 q = 1) : d16967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17121, d16967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17121, d16967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d173704 q = 1) : d128359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128376, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d173704 q = 1) : d128367 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d128367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d128367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d173704 q = 1) : d128368 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d128368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d128368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d173704 q = 1) : d128369 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d128369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d128369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39207 (p : Pattern) (ha : d128385 p = 1) (hb : d173704 p = 1) : d175383 p = 1 := by
  have h0 (q : Pattern) (ha : d128374 q = 1) (hb : d173704 q = 1) : d128374 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128380 q = 1) (hb : d173704 q = 1) : d128370 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d128370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128380, d128370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39206 q ha hb
  have h3 (q : Pattern) (ha : d17137 q = 1) (hb : d173704 q = 1) : d16999 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17137, d16999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17137, d16999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39194 q ha hb
  have h4 (q : Pattern) (ha : d128381 q = 1) (hb : d173704 q = 1) : d128371 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d128371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128381, d128371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128382 q = 1) (hb : d173704 q = 1) : d128372 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d128372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128382, d128372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128383 q = 1) (hb : d173704 q = 1) : d128373 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d128373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128383, d128373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128384 q = 1) (hb : d173704 q = 1) : d175382 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d175382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128384, d175382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128385 q = 1) (hb : d173704 q = 1) : d175383 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d175383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128385, d175383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39208 (p : Pattern) (ha : d128391 p = 1) (hb : d173704 p = 1) : d175389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d173704 q = 1) : d175384 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d175384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d175384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39207 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d173704 q = 1) : d175385 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d175385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d175385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d173704 q = 1) : d175386 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d175386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d175386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d173704 q = 1) : d175387 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d175387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d175387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d173704 q = 1) : d175388 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d175388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d175388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d173704 q = 1) : d175389 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d175389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d175389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39209 (p : Pattern) (ha : d15813 p = 1) (hb : d173704 p = 1) : d15563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2347 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2066 q = 1) (hb : d131097 q = 1) : d2066 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2348 q = 1) (hb : d173703 q = 1) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d173703, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2348, d173703, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2349 q = 1) (hb : d173704 q = 1) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d173704, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2349, d173704, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2355 q = 1) (hb : d173704 q = 1) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2355, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15791 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10414 q = 1) (hb : d131097 q = 1) : d10414 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15792 q = 1) (hb : d173703 q = 1) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d173703, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15792, d173703, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15793 q = 1) (hb : d173704 q = 1) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d173704, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15793, d173704, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d15794 q = 1) (hb : d173704 q = 1) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15794, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15813 q = 1) (hb : d173704 q = 1) : d15563 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15813, d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39210 (p : Pattern) (ha : d17396 p = 1) (hb : d173704 p = 1) : d17161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2341 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2054 q = 1) (hb : d131097 q = 1) : d2054 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2342 q = 1) (hb : d173703 q = 1) : d2055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d173703, d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2342, d173703, d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2343 q = 1) (hb : d173704 q = 1) : d2056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d173704, d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2343, d173704, d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17392 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10393 q = 1) (hb : d131097 q = 1) : d10393 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17393 q = 1) (hb : d173703 q = 1) : d17158 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17393, d173703, d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17393, d173703, d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17394 q = 1) (hb : d173704 q = 1) : d17159 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17394, d173704, d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17394, d173704, d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d17395 q = 1) (hb : d173704 q = 1) : d17160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17395, d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17395, d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15776 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10373 q = 1) (hb : d131097 q = 1) : d10373 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15777 q = 1) (hb : d173703 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d15777, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15778 q = 1) (hb : d173704 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15778, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15779 q = 1) (hb : d173704 q = 1) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15779, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17396 q = 1) (hb : d173704 q = 1) : d17161 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17396, d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17396, d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro39211 (p : Pattern) (ha : d17422 p = 1) (hb : d173704 p = 1) : d17178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17417 q = 1) (hb : d173704 q = 1) : d17169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
    | true =>
      simp only [d17417, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39209 q ha hb
  have h2 (q : Pattern) (ha : d17418 q = 1) (hb : d173704 q = 1) : d17170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17419 q = 1) (hb : d173704 q = 1) : d17171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17420 q = 1) (hb : d173704 q = 1) : d17172 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17420, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17421 q = 1) (hb : d173704 q = 1) : d17177 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d17177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17421, d17177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17422 q = 1) (hb : d173704 q = 1) : d17178 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17422, d17178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17422, d17178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39212 (p : Pattern) (ha : d17494 p = 1) (hb : d173704 p = 1) : d17198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17423 q = 1) (hb : d173704 q = 1) : d17179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d17179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39211 q ha hb
    | true =>
      simp only [d17423, d17179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17424 q = 1) (hb : d173704 q = 1) : d17180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d17180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d17180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17491 q = 1) (hb : d173704 q = 1) : d17185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17491, d17185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17491, d17185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17492 q = 1) (hb : d173704 q = 1) : d17186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17492, d17186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17492, d17186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17493 q = 1) (hb : d173704 q = 1) : d17187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17493, d17187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17493, d17187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17494 q = 1) (hb : d173704 q = 1) : d17198 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17494, d17198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17494, d17198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39213 (p : Pattern) (ha : d17500 p = 1) (hb : d173704 p = 1) : d17363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17495 q = 1) (hb : d173704 q = 1) : d17349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17495, d17349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39212 q ha hb
    | true =>
      simp only [d17495, d17349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17496 q = 1) (hb : d173704 q = 1) : d17350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17496, d17350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17496, d17350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17497 q = 1) (hb : d173704 q = 1) : d17351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17497, d17351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17497, d17351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17498 q = 1) (hb : d173704 q = 1) : d17352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17498, d17352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17498, d17352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17499 q = 1) (hb : d173704 q = 1) : d17353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17499, d17353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17499, d17353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17500 q = 1) (hb : d173704 q = 1) : d17363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17500, d17363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17500, d17363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39214 (p : Pattern) (ha : d15795 p = 1) (hb : d173704 p = 1) : d15558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6644 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5248 q = 1) (hb : d131097 q = 1) : d5248 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6645 q = 1) (hb : d173703 q = 1) : d5249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d173703, d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6645, d173703, d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6646 q = 1) (hb : d173704 q = 1) : d5250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d173704, d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6646, d173704, d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6647 q = 1) (hb : d173704 q = 1) : d5251 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6647, d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15791 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10414 q = 1) (hb : d131097 q = 1) : d10414 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15792 q = 1) (hb : d173703 q = 1) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d173703, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15792, d173703, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15793 q = 1) (hb : d173704 q = 1) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d173704, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15793, d173704, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d15794 q = 1) (hb : d173704 q = 1) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15794, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15795 q = 1) (hb : d173704 q = 1) : d15558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15795, d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39215 (p : Pattern) (ha : d17375 p = 1) (hb : d173704 p = 1) : d17229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2332 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2145 q = 1) (hb : d131097 q = 1) : d2145 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2333 q = 1) (hb : d173703 q = 1) : d2146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d173703, d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2333, d173703, d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2334 q = 1) (hb : d173704 q = 1) : d2147 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d173704, d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2334, d173704, d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17370 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10345 q = 1) (hb : d131097 q = 1) : d10345 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17371 q = 1) (hb : d173703 q = 1) : d17225 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d173703, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17371, d173703, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17372 q = 1) (hb : d173704 q = 1) : d17226 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d173704, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17372, d173704, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d17373 q = 1) (hb : d173704 q = 1) : d17227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17373, d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13814 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10355 q = 1) (hb : d131097 q = 1) : d10355 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d13815 q = 1) (hb : d173703 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d13815, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13816 q = 1) (hb : d173704 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13816, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d17374 q = 1) (hb : d173704 q = 1) : d17228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17374, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17375 q = 1) (hb : d173704 q = 1) : d17229 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17375, d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17375, d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro39216 (p : Pattern) (ha : d17382 p = 1) (hb : d173704 p = 1) : d17157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2336 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2036 q = 1) (hb : d131097 q = 1) : d2036 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2337 q = 1) (hb : d173703 q = 1) : d2037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d173703, d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2337, d173703, d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2338 q = 1) (hb : d173704 q = 1) : d2038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d173704, d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2338, d173704, d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17377 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d131097 q = 1) : d10366 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17378 q = 1) (hb : d173703 q = 1) : d17153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d173703, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d17378, d173703, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17379 q = 1) (hb : d173704 q = 1) : d17154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d173704, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17379, d173704, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d17380 q = 1) (hb : d173704 q = 1) : d17155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17380, d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13814 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10355 q = 1) (hb : d131097 q = 1) : d10355 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d13815 q = 1) (hb : d173703 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d13815, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13816 q = 1) (hb : d173704 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13816, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15776 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10373 q = 1) (hb : d131097 q = 1) : d10373 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15777 q = 1) (hb : d173703 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d15777, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15778 q = 1) (hb : d173704 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15778, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d17381 q = 1) (hb : d173704 q = 1) : d17156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17381, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17382 q = 1) (hb : d173704 q = 1) : d17157 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17382, d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17382, d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro39217 (p : Pattern) (ha : d17386 p = 1) (hb : d173704 p = 1) : d17233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13814 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10355 q = 1) (hb : d131097 q = 1) : d10355 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13815 q = 1) (hb : d173703 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13815, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13816 q = 1) (hb : d173704 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13816, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15776 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10373 q = 1) (hb : d131097 q = 1) : d10373 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15777 q = 1) (hb : d173703 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d15777, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15778 q = 1) (hb : d173704 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15778, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d17381 q = 1) (hb : d173704 q = 1) : d17156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17381, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15779 q = 1) (hb : d173704 q = 1) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15779, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17386 q = 1) (hb : d173704 q = 1) : d17233 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17386, d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro39218 (p : Pattern) (ha : d17405 p = 1) (hb : d173704 p = 1) : d17239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d173704 q = 1) : d17230 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39215 q ha hb
    | true =>
      simp only [d17383, d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39216 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d173704 q = 1) : d17231 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d17231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d17231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d173704 q = 1) : d17232 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d17232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d17232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d173704 q = 1) : d17234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39216 q ha hb
    | true =>
      simp only [d17387, d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39217 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d173704 q = 1) : d17235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d17235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d17235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d173704 q = 1) : d17236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d17236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d17236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d173704 q = 1) : d17237 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d17237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d17237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d173704 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39216 q ha hb
    | true =>
      simp only [d17397, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d173704 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d173704 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17400 q = 1) (hb : d173704 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
    | true =>
      simp only [d17400, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39214 q ha hb
  have h12 (q : Pattern) (ha : d17401 q = 1) (hb : d173704 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17402 q = 1) (hb : d173704 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17403 q = 1) (hb : d173704 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17404 q = 1) (hb : d173704 q = 1) : d17238 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d17238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d17238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17405 q = 1) (hb : d173704 q = 1) : d17239 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17405, d17239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17405, d17239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro39219 (p : Pattern) (ha : d17410 p = 1) (hb : d173704 p = 1) : d17244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d173704 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39216 q ha hb
    | true =>
      simp only [d17397, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d173704 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d173704 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d173704 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
    | true =>
      simp only [d17400, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39214 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d173704 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d173704 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d173704 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17408 q = 1) (hb : d173704 q = 1) : d17242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d17242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17408, d17242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17409 q = 1) (hb : d173704 q = 1) : d17243 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d17243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17409, d17243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17410 q = 1) (hb : d173704 q = 1) : d17244 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17410, d17244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17410, d17244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39220 (p : Pattern) (ha : d17416 p = 1) (hb : d173704 p = 1) : d17323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17406 q = 1) (hb : d173704 q = 1) : d17240 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17406, d17240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39218 q ha hb
    | true =>
      simp only [d17406, d17240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17407 q = 1) (hb : d173704 q = 1) : d17241 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17407, d17241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17407, d17241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17411 q = 1) (hb : d173704 q = 1) : d17245 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d17245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39219 q ha hb
    | true =>
      simp only [d17411, d17245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17412 q = 1) (hb : d173704 q = 1) : d17246 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d17246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d17246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17413 q = 1) (hb : d173704 q = 1) : d17247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17413, d17247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17413, d17247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17414 q = 1) (hb : d173704 q = 1) : d17248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17414, d17248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17414, d17248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17415 q = 1) (hb : d173704 q = 1) : d17249 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17415, d17249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17415, d17249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17416 q = 1) (hb : d173704 q = 1) : d17323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17416, d17323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17416, d17323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39221 (p : Pattern) (ha : d17428 p = 1) (hb : d173704 p = 1) : d17324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17411 q = 1) (hb : d173704 q = 1) : d17245 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d17245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39219 q ha hb
    | true =>
      simp only [d17411, d17245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17412 q = 1) (hb : d173704 q = 1) : d17246 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d17246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d17246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d173704 q = 1) : d17179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d17179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39211 q ha hb
    | true =>
      simp only [d17423, d17179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d173704 q = 1) : d17180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d17180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d17180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17425 q = 1) (hb : d173704 q = 1) : d17251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17425, d17251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17425, d17251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17426 q = 1) (hb : d173704 q = 1) : d17252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17426, d17252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17426, d17252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17427 q = 1) (hb : d173704 q = 1) : d17253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17427, d17253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17427, d17253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17428 q = 1) (hb : d173704 q = 1) : d17324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17428, d17324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17428, d17324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39222 (p : Pattern) (ha : d13843 p = 1) (hb : d173704 p = 1) : d13614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2347 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2066 q = 1) (hb : d131097 q = 1) : d2066 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2348 q = 1) (hb : d173703 q = 1) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d173703, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2348, d173703, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2349 q = 1) (hb : d173704 q = 1) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d173704, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2349, d173704, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2355 q = 1) (hb : d173704 q = 1) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2355, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13843 q = 1) (hb : d173704 q = 1) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13843, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro39223 (p : Pattern) (ha : d17477 p = 1) (hb : d173704 p = 1) : d17299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d173704 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39216 q ha hb
    | true =>
      simp only [d17397, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d173704 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d173704 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d173704 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
    | true =>
      simp only [d17400, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39214 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d173704 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d173704 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d173704 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17472 q = 1) (hb : d173704 q = 1) : d17294 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39210 q ha hb
    | true =>
      simp only [d17472, d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39222 q ha hb
  have h9 (q : Pattern) (ha : d17473 q = 1) (hb : d173704 q = 1) : d17295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d17295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d17295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17474 q = 1) (hb : d173704 q = 1) : d17296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d17296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d17296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17475 q = 1) (hb : d173704 q = 1) : d17297 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d17297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17475, d17297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17476 q = 1) (hb : d173704 q = 1) : d17298 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d17298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17476, d17298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17477 q = 1) (hb : d173704 q = 1) : d17299 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17477, d17299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17477, d17299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39224 (p : Pattern) (ha : d17483 p = 1) (hb : d173704 p = 1) : d17330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17478 q = 1) (hb : d173704 q = 1) : d17300 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17478, d17300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39223 q ha hb
    | true =>
      simp only [d17478, d17300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17479 q = 1) (hb : d173704 q = 1) : d17301 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17479, d17301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17479, d17301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17480 q = 1) (hb : d173704 q = 1) : d17302 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17480, d17302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17480, d17302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17481 q = 1) (hb : d173704 q = 1) : d17303 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17481, d17303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17481, d17303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17482 q = 1) (hb : d173704 q = 1) : d17304 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17482, d17304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17482, d17304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17483 q = 1) (hb : d173704 q = 1) : d17330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17483, d17330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17483, d17330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39225 (p : Pattern) (ha : d128422 p = 1) (hb : d173704 p = 1) : d128412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17429 q = 1) (hb : d173704 q = 1) : d17325 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17429, d17325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39220 q ha hb
    | true =>
      simp only [d17429, d17325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39221 q ha hb
  have h2 (q : Pattern) (ha : d128418 q = 1) (hb : d173704 q = 1) : d128401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128418, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17484 q = 1) (hb : d173704 q = 1) : d17331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17484, d17331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39224 q ha hb
    | true =>
      simp only [d17484, d17331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17485 q = 1) (hb : d173704 q = 1) : d17332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17485, d17332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17485, d17332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d173704 q = 1) : d128402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128419, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d173704 q = 1) : d128410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d128410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d128410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d173704 q = 1) : d128411 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d128411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d128411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d173704 q = 1) : d128412 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d128412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d128412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39226 (p : Pattern) (ha : d128428 p = 1) (hb : d173704 p = 1) : d175395 p = 1 := by
  have h0 (q : Pattern) (ha : d128417 q = 1) (hb : d173704 q = 1) : d128417 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128423 q = 1) (hb : d173704 q = 1) : d128413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d128413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128423, d128413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39225 q ha hb
  have h3 (q : Pattern) (ha : d17501 q = 1) (hb : d173704 q = 1) : d17364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17501, d17364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17501, d17364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39213 q ha hb
  have h4 (q : Pattern) (ha : d128424 q = 1) (hb : d173704 q = 1) : d128414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d128414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128424, d128414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128425 q = 1) (hb : d173704 q = 1) : d128415 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d128415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128425, d128415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d128426 q = 1) (hb : d173704 q = 1) : d128416 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d128416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128426, d128416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d128427 q = 1) (hb : d173704 q = 1) : d175394 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d175394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128427, d175394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d128428 q = 1) (hb : d173704 q = 1) : d175395 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d175395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128428, d175395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39227 (p : Pattern) (ha : d128434 p = 1) (hb : d173704 p = 1) : d175401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d173704 q = 1) : d175396 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d175396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d175396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39226 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d173704 q = 1) : d175397 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d175397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d175397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d173704 q = 1) : d175398 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d175398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d175398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d173704 q = 1) : d175399 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d175399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d175399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d173704 q = 1) : d175400 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d175400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d175400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d173704 q = 1) : d175401 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d175401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d175401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39228 (p : Pattern) (ha : d128440 p = 1) (hb : d173704 p = 1) : d175407 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d173704 q = 1) : d175360 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d175360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39141 q ha hb
    | true =>
      simp only [d128269, d175360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39154 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d173704 q = 1) : d175369 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d175369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d175369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39170 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d173704 q = 1) : d175370 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d175370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d175370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d173704 q = 1) : d175379 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d175379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d175379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39189 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d173704 q = 1) : d175380 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d175380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d175380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d173704 q = 1) : d175381 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d175381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d175381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d173704 q = 1) : d175390 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d175390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d175390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39208 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d173704 q = 1) : d175391 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d175391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d175391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d173704 q = 1) : d175392 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d175392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d175392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d173704 q = 1) : d175393 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d175393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d175393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d173704 q = 1) : d175402 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d175402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d175402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39227 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d173704 q = 1) : d175403 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d175403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d175403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d173704 q = 1) : d175404 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d175404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d175404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d173704 q = 1) : d175405 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d175405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d175405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d173704 q = 1) : d175406 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d175406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d175406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d173704 q = 1) : d175407 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d175407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d175407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro39229 (p : Pattern) (ha : d128446 p = 1) (hb : d173704 p = 1) : d175413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d173704 q = 1) : d175408 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d175408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39228 q ha hb
    | true =>
      simp only [d128441, d175408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d173704 q = 1) : d175409 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d175409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d175409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d173704 q = 1) : d175410 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d175410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d175410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d173704 q = 1) : d175411 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d175411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d175411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d173704 q = 1) : d175412 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d175412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d175412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d173704 q = 1) : d175413 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d175413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d175413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39230 (p : Pattern) (ha : d128452 p = 1) (hb : d173704 p = 1) : d175419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d173704 q = 1) : d175414 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d175414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39229 q ha hb
    | true =>
      simp only [d128447, d175414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d173704 q = 1) : d175415 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d175415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d175415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d173704 q = 1) : d175416 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d175416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d175416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d173704 q = 1) : d175417 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d175417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d175417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d173704 q = 1) : d175418 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d175418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d175418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d173704 q = 1) : d175419 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d175419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d175419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39231 (p : Pattern) (ha : d128458 p = 1) (hb : d173704 p = 1) : d175425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d173704 q = 1) : d175420 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d175420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39230 q ha hb
    | true =>
      simp only [d128453, d175420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d173704 q = 1) : d175421 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d175421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d175421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d173704 q = 1) : d175422 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d175422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d175422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d173704 q = 1) : d175423 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d175423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d175423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d173704 q = 1) : d175424 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d175424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d175424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128458 q = 1) (hb : d173704 q = 1) : d175425 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d175425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d175425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39232 (p : Pattern) (ha : d128464 p = 1) (hb : d173704 p = 1) : d175431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d173704 q = 1) : d175426 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d175426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39231 q ha hb
    | true =>
      simp only [d128459, d175426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d173704 q = 1) : d175427 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d175427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d175427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d173704 q = 1) : d175428 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d175428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d175428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d173704 q = 1) : d175429 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d175429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d175429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d173704 q = 1) : d175430 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d175430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d175430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d173704 q = 1) : d175431 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d175431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d175431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39233 (p : Pattern) (ha : d128470 p = 1) (hb : d173704 p = 1) : d175437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d173704 q = 1) : d175432 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d175432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39232 q ha hb
    | true =>
      simp only [d128465, d175432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d173704 q = 1) : d175433 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d175433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d175433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d173704 q = 1) : d175434 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d175434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d175434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d173704 q = 1) : d175435 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d175435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d175435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d173704 q = 1) : d175436 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d175436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d175436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d173704 q = 1) : d175437 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d175437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d175437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39234 (p : Pattern) (ha : d128476 p = 1) (hb : d173704 p = 1) : d175443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d173704 q = 1) : d175438 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d175438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39233 q ha hb
    | true =>
      simp only [d128471, d175438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d173704 q = 1) : d175439 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d175439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d175439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d173704 q = 1) : d175440 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d175440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d175440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d173704 q = 1) : d175441 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d175441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d175441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d173704 q = 1) : d175442 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d175442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d175442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d173704 q = 1) : d175443 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d175443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d175443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39235 (p : Pattern) (ha : d128482 p = 1) (hb : d173704 p = 1) : d175449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d173704 q = 1) : d175444 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d175444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39234 q ha hb
    | true =>
      simp only [d128477, d175444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d173704 q = 1) : d175445 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d175445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d175445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d173704 q = 1) : d175446 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d175446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d175446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d173704 q = 1) : d175447 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d175447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d175447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d173704 q = 1) : d175448 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d175448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d175448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d173704 q = 1) : d175449 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d175449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d175449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39236 (p : Pattern) (ha : d30 p = 1) (hb : d174650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d174648 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d174648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28, d174648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d29 q = 1) (hb : d174649 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d174649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29, d174649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d30 q = 1) (hb : d174650 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, d174650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30, d174650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro39237 (p : Pattern) (ha : d36 p = 1) (hb : d174656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d174651 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d174651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39236 q ha hb
    | true =>
      simp only [d31, d174651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d174652 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d174652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d174652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d174653 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d174653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d174653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d174654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d174654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, d174654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d174655 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, d174655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, d174655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d174656 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, d174656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, d174656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39238 (p : Pattern) (ha : d49 p = 1) (hb : d174662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d174657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d174657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39237 q ha hb
    | true =>
      simp only [d37, d174657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d174658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d174658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d174658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d174659 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d174659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, d174659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d174660 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d174660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, d174660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d174661 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, d174661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, d174661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d174662 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, d174662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, d174662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39239 (p : Pattern) (ha : d60 p = 1) (hb : d174668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d174663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d174663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39238 q ha hb
    | true =>
      simp only [d50, d174663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d174664 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d174664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, d174664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d174665 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, d174665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, d174665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d174666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, d174666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, d174666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d174667 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, d174667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, d174667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d174668 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, d174668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, d174668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39240 (p : Pattern) (ha : d174674 p = 1) (hb : d175332 p = 1) : d2672 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d65 q = 1) : d65 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61 q = 1) (hb : d174669 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, d174669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61, d174669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39239 q ha hb
  have h3 (q : Pattern) (ha : d62 q = 1) (hb : d174670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, d174670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62, d174670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d63 q = 1) (hb : d174671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, d174671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d63, d174671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d64 q = 1) (hb : d174672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, d174672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d64, d174672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d174673 q = 1) (hb : d175331 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174673, d175331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d174673, d175331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d174674 q = 1) (hb : d175332 q = 1) : d2672 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174674, d175332, d2672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174674, d175332, d2672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39241 (p : Pattern) (ha : d144 p = 1) (hb : d174681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d141 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142 q = 1) (hb : d174679 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d174679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d142, d174679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d27 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d174648 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d174648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28, d174648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d143 q = 1) (hb : d174680 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d174680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d143, d174680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29 q = 1) (hb : d174649 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d174649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29, d174649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d144 q = 1) (hb : d174681 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d174681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d144, d174681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro39242 (p : Pattern) (ha : d150 p = 1) (hb : d174687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d174682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39241 q ha hb
    | true =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39236 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d174683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d174684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d174651 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d174651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39236 q ha hb
    | true =>
      simp only [d31, d174651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d174652 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d174652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d174652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d174653 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d174653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d174653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d174685 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d174685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148, d174685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d174654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d174654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d174654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d149 q = 1) (hb : d174686 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d174686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149, d174686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150 q = 1) (hb : d174687 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d174687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150, d174687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39243 (p : Pattern) (ha : d203 p = 1) (hb : d174693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d174688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d174688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39242 q ha hb
    | true =>
      simp only [d151, d174688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d174689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d174689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d174689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d174657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d174657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39237 q ha hb
    | true =>
      simp only [d37, d174657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d174658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d174658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d174658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d174690 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d174690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d174690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d174691 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d174691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d174691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d174692 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d174692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d174692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d203 q = 1) (hb : d174693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d174693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d203, d174693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39244 (p : Pattern) (ha : d4349 p = 1) (hb : d174699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d174694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d174694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39243 q ha hb
    | true =>
      simp only [d204, d174694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39238 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d174663 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d174695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d174695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4340, d174695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d174663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d174663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39238 q ha hb
    | true =>
      simp only [d50, d174663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d174664 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d174664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d174664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4341 q = 1) (hb : d174696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d174696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d174696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4342 q = 1) (hb : d174697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d174697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d174697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4343 q = 1) (hb : d174698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d174698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d174698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4349 q = 1) (hb : d174699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d174699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d174699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39245 (p : Pattern) (ha : d174705 p = 1) (hb : d175338 p = 1) : d54298 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d51651 q = 1) : d51651 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4350 q = 1) (hb : d174700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d174700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4350, d174700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39244 q ha hb
  have h3 (q : Pattern) (ha : d4351 q = 1) (hb : d174701 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d174701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4351, d174701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d4352 q = 1) (hb : d174702 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d174702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4352, d174702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d4353 q = 1) (hb : d174703 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d174703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4353, d174703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d174704 q = 1) (hb : d175337 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174704, d175337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d174704, d175337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d174705 q = 1) (hb : d175338 q = 1) : d54298 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174705, d175338, d54298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d174705, d175338, d54298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro39246 (p : Pattern) (ha : d406 p = 1) (hb : d174745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d174663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d174663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39238 q ha hb
    | true =>
      simp only [d50, d174663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d174741 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d174741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, d174741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d174742 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d174742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, d174742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d174743 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d174743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d174743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d174744 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d174744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d174744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d174745 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d174745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d174745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39247 (p : Pattern) (ha : d5355 p = 1) (hb : d174733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d174688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d174688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39242 q ha hb
    | true =>
      simp only [d151, d174688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d174689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d174689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d174689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d174730 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d174730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d174730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d174731 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d174731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d174731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d174732 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d174732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d174732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d174733 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d174733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d174733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39248 (p : Pattern) (ha : d15966 p = 1) (hb : d174715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322 q = 1) (hb : d174711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d174711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322, d174711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d140 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d141 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142 q = 1) (hb : d174679 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d174679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d142, d174679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d323 q = 1) (hb : d174712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d174712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d323, d174712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9384 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h15 (q : Pattern) (ha : d12493 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12494 q = 1) (hb : d174713 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d174713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12494, d174713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d26 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h20 (q : Pattern) (ha : d27 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d28 q = 1) (hb : d174648 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d174648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28, d174648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d12495 q = 1) (hb : d174714 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d174714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12495, d174714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d15966 q = 1) (hb : d174715 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d174715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15966, d174715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39249 (p : Pattern) (ha : d15972 p = 1) (hb : d174721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d174716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d174716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39248 q ha hb
    | true =>
      simp only [d15967, d174716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39241 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d174717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d174717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d174717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d174718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d174718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d174718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d174682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39241 q ha hb
    | true =>
      simp only [d145, d174682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39236 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d174683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d174683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d174684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d174684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15970 q = 1) (hb : d174719 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d174719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d174719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d174651 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d174651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39236 q ha hb
    | true =>
      simp only [d31, d174651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d174652 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d174652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d174652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d174653 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d174653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d174653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148 q = 1) (hb : d174685 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d174685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148, d174685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15971 q = 1) (hb : d174720 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d174720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15971, d174720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15972 q = 1) (hb : d174721 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d174721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15972, d174721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
end NetHack.Soko22Hazard87
