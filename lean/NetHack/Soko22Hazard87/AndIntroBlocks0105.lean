import NetHack.Soko22Hazard87.AndIntroBlocks0104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro26250 (p : Pattern) (ha : d109251 p = 1) (hb : d112686 p = 1) : d142592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11943 q = 1) (hb : d112686 q = 1) : d142245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25944 q ha hb
    | true =>
      simp only [d11943, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25945 q ha hb
  have h2 (q : Pattern) (ha : d11944 q = 1) (hb : d112686 q = 1) : d142246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11945 q = 1) (hb : d112686 q = 1) : d142247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11945, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11946 q = 1) (hb : d112686 q = 1) : d142248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11947 q = 1) (hb : d112686 q = 1) : d142249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109251 q = 1) (hb : d112686 q = 1) : d142592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109251, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109251, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26251 (p : Pattern) (ha : d109262 p = 1) (hb : d112686 p = 1) : d142603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109257 q = 1) (hb : d112686 q = 1) : d142598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109257, d142598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25974 q ha hb
    | true =>
      simp only [d109257, d142598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25951 q ha hb
  have h2 (q : Pattern) (ha : d109258 q = 1) (hb : d112686 q = 1) : d142599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109258, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109258, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109259 q = 1) (hb : d112686 q = 1) : d142600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109259, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109259, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109260 q = 1) (hb : d112686 q = 1) : d142601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109260, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109260, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109261 q = 1) (hb : d112686 q = 1) : d142602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109261, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109261, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109262 q = 1) (hb : d112686 q = 1) : d142603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109262, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109262, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26252 (p : Pattern) (ha : d109268 p = 1) (hb : d112686 p = 1) : d142609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11949 q = 1) (hb : d112686 q = 1) : d142251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25943 q ha hb
    | true =>
      simp only [d11949, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25946 q ha hb
  have h2 (q : Pattern) (ha : d11950 q = 1) (hb : d112686 q = 1) : d142252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11950, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109249 q = 1) (hb : d112686 q = 1) : d142590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109249, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109249, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109250 q = 1) (hb : d112686 q = 1) : d142591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109250, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109250, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109252 q = 1) (hb : d112686 q = 1) : d142593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109252, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109252, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26250 q ha hb
  have h6 (q : Pattern) (ha : d109253 q = 1) (hb : d112686 q = 1) : d142594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109253, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109253, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109254 q = 1) (hb : d112686 q = 1) : d142595 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109254, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109254, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109255 q = 1) (hb : d112686 q = 1) : d142596 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109255, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109255, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109256 q = 1) (hb : d112686 q = 1) : d142597 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109256, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109256, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109263 q = 1) (hb : d112686 q = 1) : d142604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109263, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109263, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26251 q ha hb
  have h11 (q : Pattern) (ha : d109264 q = 1) (hb : d112686 q = 1) : d142605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109264, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109264, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109265 q = 1) (hb : d112686 q = 1) : d142606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109265, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109265, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109266 q = 1) (hb : d112686 q = 1) : d142607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109266, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109266, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109267 q = 1) (hb : d112686 q = 1) : d142608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109267, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109267, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109268 q = 1) (hb : d112686 q = 1) : d142609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109268, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109268, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26253 (p : Pattern) (ha : d109274 p = 1) (hb : d112686 p = 1) : d142615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109269 q = 1) (hb : d112686 q = 1) : d142610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109269, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109269, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26252 q ha hb
  have h2 (q : Pattern) (ha : d109270 q = 1) (hb : d112686 q = 1) : d142611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109270, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109270, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109271 q = 1) (hb : d112686 q = 1) : d142612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109271, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109271, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109272 q = 1) (hb : d112686 q = 1) : d142613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109272, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109272, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109273 q = 1) (hb : d112686 q = 1) : d142614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109273, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109273, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109274 q = 1) (hb : d112686 q = 1) : d142615 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109274, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109274, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26254 (p : Pattern) (ha : d109280 p = 1) (hb : d112686 p = 1) : d142621 p = 1 := by
  have h0 (q : Pattern) (ha : d109161 q = 1) (hb : d112686 q = 1) : d142502 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109161, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26233 q ha hb
    | true =>
      simp only [d109161, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26237 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d109188 q = 1) (hb : d112686 q = 1) : d142529 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109188, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109188, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26241 q ha hb
  have h3 (q : Pattern) (ha : d109189 q = 1) (hb : d112686 q = 1) : d142530 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109189, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109189, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109216 q = 1) (hb : d112686 q = 1) : d142557 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109216, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109216, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26245 q ha hb
  have h5 (q : Pattern) (ha : d109217 q = 1) (hb : d112686 q = 1) : d142558 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109217, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109217, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109218 q = 1) (hb : d112686 q = 1) : d142559 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109218, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109218, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109245 q = 1) (hb : d112686 q = 1) : d142586 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109245, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109245, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26249 q ha hb
  have h8 (q : Pattern) (ha : d109246 q = 1) (hb : d112686 q = 1) : d142587 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109246, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109246, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109247 q = 1) (hb : d112686 q = 1) : d142588 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109247, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109247, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109248 q = 1) (hb : d112686 q = 1) : d142589 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109248, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109248, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109275 q = 1) (hb : d112686 q = 1) : d142616 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109275, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109275, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26253 q ha hb
  have h12 (q : Pattern) (ha : d109276 q = 1) (hb : d112686 q = 1) : d142617 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109276, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109276, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109277 q = 1) (hb : d112686 q = 1) : d142618 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109277, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109277, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109278 q = 1) (hb : d112686 q = 1) : d142619 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109278, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109278, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109279 q = 1) (hb : d112686 q = 1) : d142620 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109279, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109279, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109280 q = 1) (hb : d112686 q = 1) : d142621 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109280, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109280, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro26255 (p : Pattern) (ha : d109286 p = 1) (hb : d112686 p = 1) : d142627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109281 q = 1) (hb : d112686 q = 1) : d142622 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109281, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26254 q ha hb
    | true =>
      simp only [d109281, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109282 q = 1) (hb : d112686 q = 1) : d142623 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109282, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109282, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109283 q = 1) (hb : d112686 q = 1) : d142624 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109283, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109283, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109284 q = 1) (hb : d112686 q = 1) : d142625 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109284, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109284, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109285 q = 1) (hb : d112686 q = 1) : d142626 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109285, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109285, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109286 q = 1) (hb : d112686 q = 1) : d142627 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109286, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109286, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26256 (p : Pattern) (ha : d109292 p = 1) (hb : d112686 p = 1) : d142633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109287 q = 1) (hb : d112686 q = 1) : d142628 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109287, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26255 q ha hb
    | true =>
      simp only [d109287, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109288 q = 1) (hb : d112686 q = 1) : d142629 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109288, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109288, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109289 q = 1) (hb : d112686 q = 1) : d142630 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109289, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109289, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109290 q = 1) (hb : d112686 q = 1) : d142631 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109290, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109290, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109291 q = 1) (hb : d112686 q = 1) : d142632 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109291, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109291, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109292 q = 1) (hb : d112686 q = 1) : d142633 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109292, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109292, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26257 (p : Pattern) (ha : d109298 p = 1) (hb : d112686 p = 1) : d142639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109293 q = 1) (hb : d112686 q = 1) : d142634 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109293, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26256 q ha hb
    | true =>
      simp only [d109293, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109294 q = 1) (hb : d112686 q = 1) : d142635 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109294, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109294, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109295 q = 1) (hb : d112686 q = 1) : d142636 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109295, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109295, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109296 q = 1) (hb : d112686 q = 1) : d142637 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109296, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109296, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109297 q = 1) (hb : d112686 q = 1) : d142638 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109297, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109297, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109298 q = 1) (hb : d112686 q = 1) : d142639 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109298, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109298, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26258 (p : Pattern) (ha : d109304 p = 1) (hb : d112686 p = 1) : d142645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109299 q = 1) (hb : d112686 q = 1) : d142640 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109299, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26257 q ha hb
    | true =>
      simp only [d109299, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109300 q = 1) (hb : d112686 q = 1) : d142641 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109300, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109300, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109301 q = 1) (hb : d112686 q = 1) : d142642 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109301, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109301, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109302 q = 1) (hb : d112686 q = 1) : d142643 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109302, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109302, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109303 q = 1) (hb : d112686 q = 1) : d142644 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109303, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109303, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109304 q = 1) (hb : d112686 q = 1) : d142645 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109304, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109304, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26259 (p : Pattern) (ha : d109310 p = 1) (hb : d112686 p = 1) : d142651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109305 q = 1) (hb : d112686 q = 1) : d142646 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109305, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26258 q ha hb
    | true =>
      simp only [d109305, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109306 q = 1) (hb : d112686 q = 1) : d142647 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109306, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109306, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109307 q = 1) (hb : d112686 q = 1) : d142648 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109307, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109307, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109308 q = 1) (hb : d112686 q = 1) : d142649 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109308, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109308, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109309 q = 1) (hb : d112686 q = 1) : d142650 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109309, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109309, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109310 q = 1) (hb : d112686 q = 1) : d142651 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109310, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109310, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26260 (p : Pattern) (ha : d109316 p = 1) (hb : d112686 p = 1) : d142657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109311 q = 1) (hb : d112686 q = 1) : d142652 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109311, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26259 q ha hb
    | true =>
      simp only [d109311, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109312 q = 1) (hb : d112686 q = 1) : d142653 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109312, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109312, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109313 q = 1) (hb : d112686 q = 1) : d142654 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109313, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109313, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109314 q = 1) (hb : d112686 q = 1) : d142655 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109314, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109314, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109315 q = 1) (hb : d112686 q = 1) : d142656 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109315, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109315, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109316 q = 1) (hb : d112686 q = 1) : d142657 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109316, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109316, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26261 (p : Pattern) (ha : d109322 p = 1) (hb : d112686 p = 1) : d142663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109317 q = 1) (hb : d112686 q = 1) : d142658 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109317, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26260 q ha hb
    | true =>
      simp only [d109317, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109318 q = 1) (hb : d112686 q = 1) : d142659 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109318, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109318, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109319 q = 1) (hb : d112686 q = 1) : d142660 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109319, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109319, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109320 q = 1) (hb : d112686 q = 1) : d142661 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109320, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109320, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109321 q = 1) (hb : d112686 q = 1) : d142662 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109321, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109321, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109322 q = 1) (hb : d112686 q = 1) : d142663 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109322, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109322, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26262 (p : Pattern) (ha : d112800 p = 1) (hb : d141366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112789 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112698 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
    | true =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d112790 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112790, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d112796 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112797 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112797, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d112798 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112798, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112799 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112799, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112800 q = 1) (hb : d141366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112800, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112800, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26263 (p : Pattern) (ha : d112819 p = 1) (hb : d141373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112698 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
    | true =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d112790 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112790, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112796 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d112797 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112797, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112798 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112798, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112799 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112799, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112805 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112809 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d112811 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d112705 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25992 q ha hb
    | true =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d112812 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d112812, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d112815 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d112816 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112816, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d112817 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112817, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d112817, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112818 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112818, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d112818, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112819 q = 1) (hb : d141373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112819, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112819, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26264 (p : Pattern) (ha : d112828 p = 1) (hb : d142453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112705 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25992 q ha hb
    | true =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d112812 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112812, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112815 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112816 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112816, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112826 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112826, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112826, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112827 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112827, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112827, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112828 q = 1) (hb : d142453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112828, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112828, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26265 (p : Pattern) (ha : d112858 p = 1) (hb : d142463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112847 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112732 q = 1) (hb : d141345 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112732, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25996 q ha hb
    | true =>
      simp only [d112732, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d112848 q = 1) (hb : d142459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112848, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112848, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112854 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112855 q = 1) (hb : d142460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112855, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112855, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112856 q = 1) (hb : d142461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112856, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112856, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112857 q = 1) (hb : d142462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112857, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112857, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112858 q = 1) (hb : d142463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112858, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112858, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26266 (p : Pattern) (ha : d112864 p = 1) (hb : d142469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112763 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112820 q = 1) (hb : d141374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112820, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26262 q ha hb
    | true =>
      simp only [d112820, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26263 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112823 q = 1) (hb : d141375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112823, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112823, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112824 q = 1) (hb : d142451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112824, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112824, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112825 q = 1) (hb : d142452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112825, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112825, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112829 q = 1) (hb : d142454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112829, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112829, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26264 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d112830 q = 1) (hb : d142455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112830, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112830, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112831 q = 1) (hb : d142456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112831, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112831, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d112832 q = 1) (hb : d142457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112832, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112832, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d112833 q = 1) (hb : d142458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112833, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112833, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112859 q = 1) (hb : d142464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112859, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112859, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26265 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d112860 q = 1) (hb : d142465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112860, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112860, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d112861 q = 1) (hb : d142466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112861, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112861, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d112862 q = 1) (hb : d142467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112862, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112862, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d112863 q = 1) (hb : d142468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112863, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112863, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d112864 q = 1) (hb : d142469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112864, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d112864, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26267 (p : Pattern) (ha : d112870 p = 1) (hb : d142475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d112744 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d112744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d112744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18822 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d112745 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d112745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d112745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d112746 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d112746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d112746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d112747 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d112747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d112747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d112748 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d112748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d112748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112865 q = 1) (hb : d142470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112865, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112865, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26266 q ha hb
  have h8 (q : Pattern) (ha : d112866 q = 1) (hb : d142471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112866, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112866, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112867 q = 1) (hb : d142472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112867, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112867, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112868 q = 1) (hb : d142473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112868, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112868, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112869 q = 1) (hb : d142474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112869, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112869, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112870 q = 1) (hb : d142475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d112870, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d112870, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro26268 (p : Pattern) (ha : d112954 p = 1) (hb : d141497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112922 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112943 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112887 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26022 q ha hb
    | true =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26023 q ha hb
  have h5 (q : Pattern) (ha : d112944 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112944, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d112950 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112951 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112951, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d112952 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112952, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112953 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112953, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112954 q = 1) (hb : d141497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112954, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112954, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26269 (p : Pattern) (ha : d112975 p = 1) (hb : d141507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112913 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112943 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112887 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26022 q ha hb
    | true =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26023 q ha hb
  have h4 (q : Pattern) (ha : d112944 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112944, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112950 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d112951 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112951, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112952 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112952, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112953 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112953, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112960 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d112967 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d112897 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26025 q ha hb
    | true =>
      simp only [d112897, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26026 q ha hb
  have h13 (q : Pattern) (ha : d112968 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d112968, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d112971 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d112972 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112972, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d112973 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112973, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d112973, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112974 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112974, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d112974, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112975 q = 1) (hb : d141507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112975, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112975, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26270 (p : Pattern) (ha : d112995 p = 1) (hb : d142478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112897 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26025 q ha hb
    | true =>
      simp only [d112897, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26026 q ha hb
  have h3 (q : Pattern) (ha : d112968 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112968, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112971 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112972 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112972, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112993 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112993, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112993, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112994 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112994, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112994, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112995 q = 1) (hb : d142478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112995, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112995, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26271 (p : Pattern) (ha : d113053 p = 1) (hb : d142489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113042 q = 1) (hb : d142484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113042, d142484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26051 q ha hb
    | true =>
      simp only [d113042, d142484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26054 q ha hb
  have h3 (q : Pattern) (ha : d113043 q = 1) (hb : d142485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113043, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113043, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113049 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113050 q = 1) (hb : d142486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113050, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113050, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113051 q = 1) (hb : d142487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113051, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113051, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113052 q = 1) (hb : d142488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113052, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113052, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113053 q = 1) (hb : d142489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113053, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113053, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26272 (p : Pattern) (ha : d113066 p = 1) (hb : d142495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112905 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112976 q = 1) (hb : d141508 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112976, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26268 q ha hb
    | true =>
      simp only [d112976, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26269 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112990 q = 1) (hb : d141509 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112990, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112990, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112991 q = 1) (hb : d142476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112991, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112991, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112992 q = 1) (hb : d142477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112992, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112992, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112996 q = 1) (hb : d142479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112996, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112996, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26270 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112998 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d112999 q = 1) (hb : d142480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112999, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112999, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113000 q = 1) (hb : d142481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113000, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113000, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113001 q = 1) (hb : d142482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113001, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113001, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113002 q = 1) (hb : d142483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113002, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113002, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113054 q = 1) (hb : d142490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113054, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113054, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26271 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113062 q = 1) (hb : d142491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113062, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113062, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113063 q = 1) (hb : d142492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113063, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113063, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113064 q = 1) (hb : d142493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113064, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113064, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113065 q = 1) (hb : d142494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113065, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113065, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113066 q = 1) (hb : d142495 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113066, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113066, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26273 (p : Pattern) (ha : d113072 p = 1) (hb : d142501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113067 q = 1) (hb : d142496 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113067, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113067, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26272 q ha hb
  have h2 (q : Pattern) (ha : d113068 q = 1) (hb : d142497 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113068, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113068, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113069 q = 1) (hb : d142498 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113069, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113069, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113070 q = 1) (hb : d142499 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113070, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113070, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113071 q = 1) (hb : d142500 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113071, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113071, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113072 q = 1) (hb : d142501 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113072, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113072, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26274 (p : Pattern) (ha : d113161 p = 1) (hb : d141676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113094 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26060 q ha hb
    | true =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26061 q ha hb
  have h5 (q : Pattern) (ha : d113151 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113151, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113157 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113158 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113158, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113159 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113159, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113160 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113160, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113161 q = 1) (hb : d141676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113161, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113161, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26275 (p : Pattern) (ha : d113182 p = 1) (hb : d141686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113094 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26060 q ha hb
    | true =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26061 q ha hb
  have h4 (q : Pattern) (ha : d113151 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113151, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113158 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113158, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113159 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113159, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113160 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113160, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113167 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113172 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113174 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113104 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26063 q ha hb
    | true =>
      simp only [d113104, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26064 q ha hb
  have h13 (q : Pattern) (ha : d113175 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113175, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113178 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113179 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113179, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113180 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113180, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113180, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113181 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113181, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113181, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113182 q = 1) (hb : d141686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113182, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113182, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26276 (p : Pattern) (ha : d113202 p = 1) (hb : d142505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113104 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26063 q ha hb
    | true =>
      simp only [d113104, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26064 q ha hb
  have h3 (q : Pattern) (ha : d113175 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113175, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113179 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113179, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113200 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113200, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113200, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113201 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113201, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113201, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113202 q = 1) (hb : d142505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113202, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113202, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26277 (p : Pattern) (ha : d113264 p = 1) (hb : d142516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113248 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113253 q = 1) (hb : d142511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113253, d142511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26089 q ha hb
    | true =>
      simp only [d113253, d142511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26092 q ha hb
  have h3 (q : Pattern) (ha : d113254 q = 1) (hb : d142512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113254, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113254, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113260 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113261 q = 1) (hb : d142513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113261, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113261, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113262 q = 1) (hb : d142514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113262, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113262, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113263 q = 1) (hb : d142515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113263, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113263, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113264 q = 1) (hb : d142516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113264, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113264, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26278 (p : Pattern) (ha : d113277 p = 1) (hb : d142522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113183 q = 1) (hb : d141687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113183, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26274 q ha hb
    | true =>
      simp only [d113183, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26275 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113196 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113197 q = 1) (hb : d141688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113197, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113197, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113198 q = 1) (hb : d142503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113198, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113198, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113199 q = 1) (hb : d142504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113199, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113199, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113203 q = 1) (hb : d142506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113203, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113203, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26276 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113205 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113206 q = 1) (hb : d142507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113206, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113206, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113207 q = 1) (hb : d142508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113207, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113207, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113208 q = 1) (hb : d142509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113208, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113208, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113209 q = 1) (hb : d142510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113209, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113209, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113265 q = 1) (hb : d142517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113265, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113265, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26277 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113272 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113273 q = 1) (hb : d142518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113273, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113273, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113274 q = 1) (hb : d142519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113274, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113274, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113275 q = 1) (hb : d142520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113275, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113275, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113276 q = 1) (hb : d142521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113276, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113276, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113277 q = 1) (hb : d142522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113277, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113277, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26279 (p : Pattern) (ha : d113283 p = 1) (hb : d142528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113278 q = 1) (hb : d142523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113278, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113278, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26278 q ha hb
  have h2 (q : Pattern) (ha : d113279 q = 1) (hb : d142524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113279, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113279, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113280 q = 1) (hb : d142525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113280, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113280, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113281 q = 1) (hb : d142526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113281, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113281, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113282 q = 1) (hb : d142527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113282, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113282, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113283 q = 1) (hb : d142528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113283, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113283, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26280 (p : Pattern) (ha : d113392 p = 1) (hb : d141863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113347 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113312 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26098 q ha hb
    | true =>
      simp only [d113312, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26099 q ha hb
  have h5 (q : Pattern) (ha : d113382 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113382, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113388 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113389 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113389, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113390 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113390, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113391 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113391, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113392 q = 1) (hb : d141863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113392, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113392, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26281 (p : Pattern) (ha : d113414 p = 1) (hb : d141873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113381 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113312 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26098 q ha hb
    | true =>
      simp only [d113312, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26099 q ha hb
  have h4 (q : Pattern) (ha : d113382 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113382, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113388 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113389 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113389, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113390 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113390, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113391 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113391, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113398 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113403 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113406 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113322 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26101 q ha hb
    | true =>
      simp only [d113322, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26102 q ha hb
  have h13 (q : Pattern) (ha : d113407 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113407, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113410 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113411 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113411, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113412 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113412, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113412, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113413 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113413, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113413, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113414 q = 1) (hb : d141873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113414, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113414, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26282 (p : Pattern) (ha : d113439 p = 1) (hb : d142533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113406 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113322 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26101 q ha hb
    | true =>
      simp only [d113322, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26102 q ha hb
  have h3 (q : Pattern) (ha : d113407 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113407, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113410 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113411 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113411, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113437 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113437, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113437, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113438 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113438, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113438, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113439 q = 1) (hb : d142533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113439, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113439, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26283 (p : Pattern) (ha : d113503 p = 1) (hb : d141990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113498 q = 1) (hb : d141977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113498, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26131 q ha hb
    | true =>
      simp only [d113498, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113499 q = 1) (hb : d141978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113499, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113499, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113489 q = 1) (hb : d141985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113489, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26129 q ha hb
    | true =>
      simp only [d113489, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113490 q = 1) (hb : d141986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113490, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113490, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113500 q = 1) (hb : d141987 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113500, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113500, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113501 q = 1) (hb : d141988 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113501, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113501, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113502 q = 1) (hb : d141989 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113502, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113502, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113503 q = 1) (hb : d141990 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113503, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113503, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26284 (p : Pattern) (ha : d113519 p = 1) (hb : d142544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113508 q = 1) (hb : d142539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113508, d142539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26283 q ha hb
    | true =>
      simp only [d113508, d142539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26134 q ha hb
  have h3 (q : Pattern) (ha : d113509 q = 1) (hb : d142540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113509, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113509, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113516 q = 1) (hb : d142541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113516, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113516, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113517 q = 1) (hb : d142542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113517, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113517, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113518 q = 1) (hb : d142543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113518, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113518, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113519 q = 1) (hb : d142544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113519, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113519, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26285 (p : Pattern) (ha : d113532 p = 1) (hb : d142550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113415 q = 1) (hb : d141874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113415, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26280 q ha hb
    | true =>
      simp only [d113415, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26281 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113433 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113434 q = 1) (hb : d141875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113434, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113434, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113435 q = 1) (hb : d142531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113435, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113435, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113436 q = 1) (hb : d142532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113436, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113436, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113440 q = 1) (hb : d142534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113440, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113440, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26282 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113442 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113443 q = 1) (hb : d142535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113443, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113443, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113444 q = 1) (hb : d142536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113444, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113444, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113445 q = 1) (hb : d142537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113445, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113445, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113446 q = 1) (hb : d142538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113446, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113446, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113520 q = 1) (hb : d142545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113520, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113520, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26284 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113527 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113528 q = 1) (hb : d142546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113528, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113528, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113529 q = 1) (hb : d142547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113529, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113529, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113530 q = 1) (hb : d142548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113530, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113530, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113531 q = 1) (hb : d142549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113531, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113531, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113532 q = 1) (hb : d142550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113532, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113532, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26286 (p : Pattern) (ha : d113538 p = 1) (hb : d142556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113533 q = 1) (hb : d142551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113533, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113533, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26285 q ha hb
  have h2 (q : Pattern) (ha : d113534 q = 1) (hb : d142552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113534, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113534, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113535 q = 1) (hb : d142553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113535, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113535, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113536 q = 1) (hb : d142554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113536, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113536, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113537 q = 1) (hb : d142555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113537, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113537, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113538 q = 1) (hb : d142556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113538, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113538, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26287 (p : Pattern) (ha : d113648 p = 1) (hb : d142051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113603 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113637 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113568 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26140 q ha hb
    | true =>
      simp only [d113568, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26141 q ha hb
  have h5 (q : Pattern) (ha : d113638 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113638, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113644 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113645 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113645, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113646 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113646, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113647 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113647, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113648 q = 1) (hb : d142051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113648, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113648, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26288 (p : Pattern) (ha : d113670 p = 1) (hb : d142061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113568 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26140 q ha hb
    | true =>
      simp only [d113568, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26141 q ha hb
  have h4 (q : Pattern) (ha : d113638 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113638, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113644 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113645 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113645, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113646 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113646, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113647 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113647, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113659 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113662 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113578 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26143 q ha hb
    | true =>
      simp only [d113578, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26144 q ha hb
  have h13 (q : Pattern) (ha : d113663 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113663, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113666 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113667 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113667, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113668 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113668, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113668, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113669 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113669, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113669, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113670 q = 1) (hb : d142061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113670, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113670, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26289 (p : Pattern) (ha : d113695 p = 1) (hb : d142562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113578 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26143 q ha hb
    | true =>
      simp only [d113578, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26144 q ha hb
  have h3 (q : Pattern) (ha : d113663 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113663, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113666 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113667 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113667, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113693 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113693, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113693, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113694 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113694, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113694, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113695 q = 1) (hb : d142562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113695, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113695, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26290 (p : Pattern) (ha : d113759 p = 1) (hb : d142178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113754 q = 1) (hb : d142165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113754, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26173 q ha hb
    | true =>
      simp only [d113754, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113755 q = 1) (hb : d142166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113755, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113755, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113745 q = 1) (hb : d142173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26171 q ha hb
    | true =>
      simp only [d113745, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113746 q = 1) (hb : d142174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113756 q = 1) (hb : d142175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113756, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113756, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113757 q = 1) (hb : d142176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113757, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113757, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113758 q = 1) (hb : d142177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113758, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113758, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113759 q = 1) (hb : d142178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113759, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113759, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26291 (p : Pattern) (ha : d113775 p = 1) (hb : d142573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113764 q = 1) (hb : d142568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113764, d142568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26290 q ha hb
    | true =>
      simp only [d113764, d142568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26176 q ha hb
  have h3 (q : Pattern) (ha : d113765 q = 1) (hb : d142569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113765, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113765, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113772 q = 1) (hb : d142570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113772, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113772, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113773 q = 1) (hb : d142571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113773, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113773, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113774 q = 1) (hb : d142572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113774, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113774, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113775 q = 1) (hb : d142573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113775, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113775, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26292 (p : Pattern) (ha : d113788 p = 1) (hb : d142579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113671 q = 1) (hb : d142062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113671, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26287 q ha hb
    | true =>
      simp only [d113671, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26288 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113690 q = 1) (hb : d142063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113690, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113690, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113691 q = 1) (hb : d142560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113691, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113691, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113692 q = 1) (hb : d142561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113692, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113692, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113696 q = 1) (hb : d142563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113696, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113696, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26289 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113698 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113699 q = 1) (hb : d142564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113699, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113699, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113700 q = 1) (hb : d142565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113700, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113700, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113701 q = 1) (hb : d142566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113701, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113701, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113702 q = 1) (hb : d142567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113702, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113702, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113776 q = 1) (hb : d142574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113776, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113776, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26291 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113783 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113784 q = 1) (hb : d142575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113784, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113784, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113785 q = 1) (hb : d142576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113785, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113785, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113786 q = 1) (hb : d142577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113786, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113786, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113787 q = 1) (hb : d142578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113787, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113787, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113788 q = 1) (hb : d142579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113788, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113788, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26293 (p : Pattern) (ha : d113794 p = 1) (hb : d142585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113789 q = 1) (hb : d142580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113789, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113789, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26292 q ha hb
  have h2 (q : Pattern) (ha : d113790 q = 1) (hb : d142581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113790, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113790, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113791 q = 1) (hb : d142582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113791, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113791, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113792 q = 1) (hb : d142583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113792, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113792, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113793 q = 1) (hb : d142584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113793, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113793, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113794 q = 1) (hb : d142585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113794, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113794, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26294 (p : Pattern) (ha : d113905 p = 1) (hb : d142240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113851 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113860 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113894 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113825 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26182 q ha hb
    | true =>
      simp only [d113825, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26183 q ha hb
  have h5 (q : Pattern) (ha : d113895 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113895, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113902 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113902, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113903 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113903, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113904 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113904, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113905 q = 1) (hb : d142240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113905, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113905, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26295 (p : Pattern) (ha : d113927 p = 1) (hb : d142250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113851 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113825 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26182 q ha hb
    | true =>
      simp only [d113825, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26183 q ha hb
  have h4 (q : Pattern) (ha : d113895 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113895, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113901 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113902 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113902, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113903 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113903, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113904 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113904, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113911 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113916 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113919 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113835 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26185 q ha hb
    | true =>
      simp only [d113835, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26186 q ha hb
  have h13 (q : Pattern) (ha : d113920 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113920, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113923 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113924 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113924, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113925 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113925, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113925, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113926 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113926, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113926, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113927 q = 1) (hb : d142250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113927, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113927, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26296 (p : Pattern) (ha : d113952 p = 1) (hb : d142592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113919 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113835 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26185 q ha hb
    | true =>
      simp only [d113835, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26186 q ha hb
  have h3 (q : Pattern) (ha : d113920 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113920, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113923 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113924 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113924, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113950 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113950, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113950, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113951 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113951, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113951, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113952 q = 1) (hb : d142592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113952, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113952, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26297 (p : Pattern) (ha : d114016 p = 1) (hb : d142367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114011 q = 1) (hb : d142354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114011, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26215 q ha hb
    | true =>
      simp only [d114011, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114012 q = 1) (hb : d142355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114012, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114012, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114002 q = 1) (hb : d142362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26213 q ha hb
    | true =>
      simp only [d114002, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114003 q = 1) (hb : d142363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114013 q = 1) (hb : d142364 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114013, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114013, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114014 q = 1) (hb : d142365 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114014, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114014, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d114015 q = 1) (hb : d142366 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114015, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d114015, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d114016 q = 1) (hb : d142367 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114016, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d114016, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26298 (p : Pattern) (ha : d114032 p = 1) (hb : d142603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d114008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d114021 q = 1) (hb : d142598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114021, d142598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26297 q ha hb
    | true =>
      simp only [d114021, d142598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26218 q ha hb
  have h3 (q : Pattern) (ha : d114022 q = 1) (hb : d142599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114022, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114022, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d114029 q = 1) (hb : d142600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114029, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114029, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d114030 q = 1) (hb : d142601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114030, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114030, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d114031 q = 1) (hb : d142602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114031, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114031, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d114032 q = 1) (hb : d142603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114032, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114032, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26299 (p : Pattern) (ha : d114045 p = 1) (hb : d142609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113928 q = 1) (hb : d142251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113928, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26294 q ha hb
    | true =>
      simp only [d113928, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26295 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113946 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113947 q = 1) (hb : d142252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113947, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113947, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113948 q = 1) (hb : d142590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113948, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113948, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113949 q = 1) (hb : d142591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113949, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113949, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113953 q = 1) (hb : d142593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113953, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113953, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26296 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113955 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113956 q = 1) (hb : d142594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113956, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113956, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113957 q = 1) (hb : d142595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113957, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113957, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113958 q = 1) (hb : d142596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113958, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113958, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113959 q = 1) (hb : d142597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113959, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113959, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114033 q = 1) (hb : d142604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114033, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d114033, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26298 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d114040 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d114041 q = 1) (hb : d142605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d114041, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d114041, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d114042 q = 1) (hb : d142606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114042, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114042, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d114043 q = 1) (hb : d142607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d114043, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d114043, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d114044 q = 1) (hb : d142608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d114044, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d114044, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d114045 q = 1) (hb : d142609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d114045, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d114045, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26300 (p : Pattern) (ha : d114051 p = 1) (hb : d142615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114046 q = 1) (hb : d142610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d114046, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114046, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26299 q ha hb
  have h2 (q : Pattern) (ha : d114047 q = 1) (hb : d142611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d114047, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114047, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114048 q = 1) (hb : d142612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d114048, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114048, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d114049 q = 1) (hb : d142613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d114049, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114049, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114050 q = 1) (hb : d142614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d114050, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114050, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114051 q = 1) (hb : d142615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d114051, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114051, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26301 (p : Pattern) (ha : d114057 p = 1) (hb : d142621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d113073 q = 1) (hb : d142502 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113073, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26267 q ha hb
    | true =>
      simp only [d113073, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26273 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113284 q = 1) (hb : d142529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113284, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113284, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26279 q ha hb
  have h3 (q : Pattern) (ha : d113285 q = 1) (hb : d142530 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113285, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d113285, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113539 q = 1) (hb : d142557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113539, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113539, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26286 q ha hb
  have h5 (q : Pattern) (ha : d113540 q = 1) (hb : d142558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113540, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113540, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113541 q = 1) (hb : d142559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113541, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113541, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113795 q = 1) (hb : d142586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113795, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113795, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26293 q ha hb
  have h8 (q : Pattern) (ha : d113796 q = 1) (hb : d142587 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113796, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113796, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113797 q = 1) (hb : d142588 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113797, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113797, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113798 q = 1) (hb : d142589 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d113798, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113798, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d114052 q = 1) (hb : d142616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d114052, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114052, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26300 q ha hb
  have h12 (q : Pattern) (ha : d114053 q = 1) (hb : d142617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d114053, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114053, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114054 q = 1) (hb : d142618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d114054, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114054, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d114055 q = 1) (hb : d142619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d114055, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114055, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d114056 q = 1) (hb : d142620 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d114056, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d114056, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d114057 q = 1) (hb : d142621 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d114057, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114057, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro26302 (p : Pattern) (ha : d114063 p = 1) (hb : d142627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114058 q = 1) (hb : d142622 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d114058, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26301 q ha hb
    | true =>
      simp only [d114058, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114059 q = 1) (hb : d142623 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d114059, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114059, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114060 q = 1) (hb : d142624 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d114060, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114060, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114061 q = 1) (hb : d142625 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d114061, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114061, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114062 q = 1) (hb : d142626 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d114062, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114062, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114063 q = 1) (hb : d142627 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d114063, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114063, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26303 (p : Pattern) (ha : d114069 p = 1) (hb : d142633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114064 q = 1) (hb : d142628 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d114064, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26302 q ha hb
    | true =>
      simp only [d114064, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114065 q = 1) (hb : d142629 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d114065, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114065, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114066 q = 1) (hb : d142630 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d114066, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114066, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114067 q = 1) (hb : d142631 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d114067, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114067, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114068 q = 1) (hb : d142632 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d114068, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114068, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114069 q = 1) (hb : d142633 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d114069, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114069, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26304 (p : Pattern) (ha : d114075 p = 1) (hb : d142639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114070 q = 1) (hb : d142634 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d114070, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26303 q ha hb
    | true =>
      simp only [d114070, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114071 q = 1) (hb : d142635 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d114071, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114071, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114072 q = 1) (hb : d142636 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d114072, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114072, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114073 q = 1) (hb : d142637 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d114073, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114073, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114074 q = 1) (hb : d142638 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d114074, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114074, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114075 q = 1) (hb : d142639 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d114075, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114075, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26305 (p : Pattern) (ha : d114081 p = 1) (hb : d142645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114076 q = 1) (hb : d142640 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d114076, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26304 q ha hb
    | true =>
      simp only [d114076, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114077 q = 1) (hb : d142641 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d114077, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114077, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114078 q = 1) (hb : d142642 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d114078, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114078, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114079 q = 1) (hb : d142643 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d114079, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114079, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114080 q = 1) (hb : d142644 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d114080, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114080, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114081 q = 1) (hb : d142645 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d114081, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114081, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26306 (p : Pattern) (ha : d114087 p = 1) (hb : d142651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114082 q = 1) (hb : d142646 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d114082, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26305 q ha hb
    | true =>
      simp only [d114082, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114083 q = 1) (hb : d142647 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d114083, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114083, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114084 q = 1) (hb : d142648 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d114084, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114084, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114085 q = 1) (hb : d142649 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d114085, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114085, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114086 q = 1) (hb : d142650 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d114086, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114086, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114087 q = 1) (hb : d142651 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d114087, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114087, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26307 (p : Pattern) (ha : d114093 p = 1) (hb : d142657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114088 q = 1) (hb : d142652 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d114088, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26306 q ha hb
    | true =>
      simp only [d114088, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114089 q = 1) (hb : d142653 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d114089, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114089, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114090 q = 1) (hb : d142654 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d114090, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114090, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114091 q = 1) (hb : d142655 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d114091, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114091, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114092 q = 1) (hb : d142656 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d114092, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114092, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114093 q = 1) (hb : d142657 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d114093, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114093, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26308 (p : Pattern) (ha : d114099 p = 1) (hb : d142663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114094 q = 1) (hb : d142658 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d114094, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26307 q ha hb
    | true =>
      simp only [d114094, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114095 q = 1) (hb : d142659 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d114095, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114095, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114096 q = 1) (hb : d142660 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d114096, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114096, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114097 q = 1) (hb : d142661 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d114097, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114097, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114098 q = 1) (hb : d142662 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d114098, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114098, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114099 q = 1) (hb : d142663 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d114099, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114099, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26309 (p : Pattern) (ha : d115280 p = 1) (hb : d141366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12325 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115276 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115276, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12346 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115277 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115277, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115278 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115278, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115279 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115279, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115280 q = 1) (hb : d141366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26310 (p : Pattern) (ha : d115285 p = 1) (hb : d141373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115276 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115276, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12346 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115277 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115277, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115278 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115278, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115279 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115279, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12355 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12359 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12361 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115281 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115281, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12367 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115282 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115282, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115283 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115283, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115284 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115284, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115285 q = 1) (hb : d141373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115285, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26311 (p : Pattern) (ha : d115292 p = 1) (hb : d142453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12361 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115281 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115281, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115282, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d142453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26312 (p : Pattern) (ha : d115302 p = 1) (hb : d142463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12399 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141345 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115298 q = 1) (hb : d142459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115298, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d142460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115299, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d142461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d142462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d142463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26313 (p : Pattern) (ha : d115308 p = 1) (hb : d142469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115286 q = 1) (hb : d141374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26309 q ha hb
    | true =>
      simp only [d115286, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26310 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12374 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115287 q = 1) (hb : d141375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115287, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115288 q = 1) (hb : d142451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115288, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115289 q = 1) (hb : d142452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115289, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115293 q = 1) (hb : d142454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115293, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26311 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115294 q = 1) (hb : d142455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115294, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115295 q = 1) (hb : d142456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115295, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115296 q = 1) (hb : d142457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115296, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115297 q = 1) (hb : d142458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115297, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115303 q = 1) (hb : d142464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115303, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26312 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115304 q = 1) (hb : d142465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115304, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115305 q = 1) (hb : d142466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115305, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115306 q = 1) (hb : d142467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115306, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115307 q = 1) (hb : d142468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115307, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115308 q = 1) (hb : d142469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115308, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26314 (p : Pattern) (ha : d115314 p = 1) (hb : d142475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d115271 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18874 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d115272 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d115273 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d115274 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d115275 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115309 q = 1) (hb : d142470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115309, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26313 q ha hb
  have h8 (q : Pattern) (ha : d115310 q = 1) (hb : d142471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115310, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115311 q = 1) (hb : d142472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115311, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115312 q = 1) (hb : d142473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115312, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115313 q = 1) (hb : d142474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115313, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115314 q = 1) (hb : d142475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d115314, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro26315 (p : Pattern) (ha : d115319 p = 1) (hb : d141497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12488 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12509 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115315 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115315, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12539 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115316 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115316, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115317 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115317, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115318 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115318, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115319 q = 1) (hb : d141497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26316 (p : Pattern) (ha : d115324 p = 1) (hb : d141507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115315 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115315, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12539 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115316 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115316, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115317 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115317, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115318 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115318, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12549 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12554 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12556 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115320 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115320, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12563 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115321 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115321, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115322 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115322, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115323 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115323, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115324 q = 1) (hb : d141507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115324, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26317 (p : Pattern) (ha : d115331 p = 1) (hb : d142478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115320 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115320, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12563 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115321, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d142478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26318 (p : Pattern) (ha : d115341 p = 1) (hb : d142489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142484 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115337 q = 1) (hb : d142485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115337, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12659 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d142486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115338, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d142487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d142488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d142489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26319 (p : Pattern) (ha : d115347 p = 1) (hb : d142495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115325 q = 1) (hb : d141508 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26315 q ha hb
    | true =>
      simp only [d115325, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26316 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12581 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115326 q = 1) (hb : d141509 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115326, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115327 q = 1) (hb : d142476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115327, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115328 q = 1) (hb : d142477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115328, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115332 q = 1) (hb : d142479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115332, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26317 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12590 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115333 q = 1) (hb : d142480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115333, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115334 q = 1) (hb : d142481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115334, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115335 q = 1) (hb : d142482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115335, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115336 q = 1) (hb : d142483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115336, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115342 q = 1) (hb : d142490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115342, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26318 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115343 q = 1) (hb : d142491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115343, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115344 q = 1) (hb : d142492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115344, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115345 q = 1) (hb : d142493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115345, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115346 q = 1) (hb : d142494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115346, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115347 q = 1) (hb : d142495 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115347, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26320 (p : Pattern) (ha : d115353 p = 1) (hb : d142501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d142496 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26319 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d142497 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d142498 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d142499 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d142500 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d142501 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26321 (p : Pattern) (ha : d115359 p = 1) (hb : d141676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12764 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115355 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115355, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12798 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115356 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115356, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115357 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115357, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115358 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115358, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115359 q = 1) (hb : d141676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26322 (p : Pattern) (ha : d115364 p = 1) (hb : d141686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115355 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115355, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115356 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115356, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115357 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115357, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115358 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115358, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12815 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115360 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115360, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12822 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115361 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115361, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115362 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115362, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115363 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115363, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115364 q = 1) (hb : d141686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115364, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26323 (p : Pattern) (ha : d115371 p = 1) (hb : d142505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115360 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115360, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12822 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115361, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d142505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26324 (p : Pattern) (ha : d115381 p = 1) (hb : d142516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142511 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115377 q = 1) (hb : d142512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115377, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d142513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115378, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d142514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d142515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d142516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26325 (p : Pattern) (ha : d115387 p = 1) (hb : d142522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115365 q = 1) (hb : d141687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26321 q ha hb
    | true =>
      simp only [d115365, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26322 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115366 q = 1) (hb : d141688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115366, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115367 q = 1) (hb : d142503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115367, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115368 q = 1) (hb : d142504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115368, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115372 q = 1) (hb : d142506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115372, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26323 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12849 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115373 q = 1) (hb : d142507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115373, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115374 q = 1) (hb : d142508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115374, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115375 q = 1) (hb : d142509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115375, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115376 q = 1) (hb : d142510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115376, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115382 q = 1) (hb : d142517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115382, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26324 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12942 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115383 q = 1) (hb : d142518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115383, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115384 q = 1) (hb : d142519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115384, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115385 q = 1) (hb : d142520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115385, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115386 q = 1) (hb : d142521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115386, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115387 q = 1) (hb : d142522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115387, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26326 (p : Pattern) (ha : d115393 p = 1) (hb : d142528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d142523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26325 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d142524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d142525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d142526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d142527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d142528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26327 (p : Pattern) (ha : d115400 p = 1) (hb : d141863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13051 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115396 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115396, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13093 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115397 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115397, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115398 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115398, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115399 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115399, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115400 q = 1) (hb : d141863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26328 (p : Pattern) (ha : d115405 p = 1) (hb : d141873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13051 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115396 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115396, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13093 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115397 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115397, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115398 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115398, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115399 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115399, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13103 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13108 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13111 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115401 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115401, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13118 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115402 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115402, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115403 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115403, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115404 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115404, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115405 q = 1) (hb : d141873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115405, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26329 (p : Pattern) (ha : d115412 p = 1) (hb : d142533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115401 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115401, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13118 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115402, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d142533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26330 (p : Pattern) (ha : d115422 p = 1) (hb : d142544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115418 q = 1) (hb : d142540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115418, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13251 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d142541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115419, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d142542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d142543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d142544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26331 (p : Pattern) (ha : d115428 p = 1) (hb : d142550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13000 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115406 q = 1) (hb : d141874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26327 q ha hb
    | true =>
      simp only [d115406, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26328 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115407 q = 1) (hb : d141875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115407, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115408 q = 1) (hb : d142531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115408, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115409 q = 1) (hb : d142532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115409, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115413 q = 1) (hb : d142534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115413, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26329 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13150 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115414 q = 1) (hb : d142535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115414, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115415 q = 1) (hb : d142536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115415, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115416 q = 1) (hb : d142537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115416, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115417 q = 1) (hb : d142538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115417, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115423 q = 1) (hb : d142545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115423, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26330 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13267 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115424 q = 1) (hb : d142546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115424, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115425 q = 1) (hb : d142547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115425, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115426 q = 1) (hb : d142548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115426, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115427 q = 1) (hb : d142549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115427, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115428 q = 1) (hb : d142550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115428, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26332 (p : Pattern) (ha : d115434 p = 1) (hb : d142556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d142551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26331 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d142552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d142553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d142554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d142555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d142556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26333 (p : Pattern) (ha : d115442 p = 1) (hb : d142051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115438 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115438, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13419 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115439 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115439, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115440 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115440, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115441 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115441, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115442 q = 1) (hb : d142051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26334 (p : Pattern) (ha : d115447 p = 1) (hb : d142061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13343 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115438 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115438, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115439 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115439, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115440 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115440, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115441 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115441, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13429 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13437 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115443 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115443, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13444 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115444 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115444, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115445 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115445, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115446 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115446, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115447 q = 1) (hb : d142061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115447, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26335 (p : Pattern) (ha : d115454 p = 1) (hb : d142562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115443 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115443, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115444 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115444, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115452 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115452, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115453 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115453, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115454 q = 1) (hb : d142562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115454, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26336 (p : Pattern) (ha : d115464 p = 1) (hb : d142573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142568 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115460 q = 1) (hb : d142569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115460, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13577 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115461 q = 1) (hb : d142570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115461, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115462 q = 1) (hb : d142571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115462, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115463 q = 1) (hb : d142572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115463, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115464 q = 1) (hb : d142573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115464, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26337 (p : Pattern) (ha : d115470 p = 1) (hb : d142579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13326 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115448 q = 1) (hb : d142062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26333 q ha hb
    | true =>
      simp only [d115448, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26334 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13467 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115449 q = 1) (hb : d142063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115449, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115450 q = 1) (hb : d142560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115450, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115451 q = 1) (hb : d142561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115451, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115455 q = 1) (hb : d142563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115455, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26335 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13476 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115456 q = 1) (hb : d142564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115456, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115457 q = 1) (hb : d142565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115457, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115458 q = 1) (hb : d142566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115458, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115459 q = 1) (hb : d142567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115459, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115465 q = 1) (hb : d142574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115465, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26336 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13593 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115466 q = 1) (hb : d142575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115466, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115467 q = 1) (hb : d142576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115467, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115468 q = 1) (hb : d142577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115468, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115469 q = 1) (hb : d142578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115469, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115470 q = 1) (hb : d142579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115470, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26338 (p : Pattern) (ha : d115476 p = 1) (hb : d142585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115471 q = 1) (hb : d142580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115471, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26337 q ha hb
  have h2 (q : Pattern) (ha : d115472 q = 1) (hb : d142581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115472, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115473 q = 1) (hb : d142582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115473, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115474 q = 1) (hb : d142583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115474, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115475 q = 1) (hb : d142584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115475, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115476 q = 1) (hb : d142585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115476, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26339 (p : Pattern) (ha : d115485 p = 1) (hb : d142240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13670 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13704 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115481 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115481, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13746 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115482 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115482, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115483 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115483, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115484 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115484, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115485 q = 1) (hb : d142240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115485, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro26340 (p : Pattern) (ha : d115490 p = 1) (hb : d142250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13661 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115481 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115481, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13746 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115482 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115482, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115483 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115483, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115484 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115484, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13756 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13761 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13764 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115486 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115486, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13771 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115487 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115487, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115488 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115488, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115489 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115489, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115490 q = 1) (hb : d142250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115490, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro26341 (p : Pattern) (ha : d115497 p = 1) (hb : d142592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115486 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115486, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115487 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115487, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115495 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115495, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115496 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115496, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115497 q = 1) (hb : d142592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115497, d142592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26342 (p : Pattern) (ha : d115507 p = 1) (hb : d142603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115503 q = 1) (hb : d142599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115503, d142599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13904 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d142600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115504, d142600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d142601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d142601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d142602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d142602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d142603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d142603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26343 (p : Pattern) (ha : d115513 p = 1) (hb : d142609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13653 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115491 q = 1) (hb : d142251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26339 q ha hb
    | true =>
      simp only [d115491, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26340 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115492 q = 1) (hb : d142252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115492, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115493 q = 1) (hb : d142590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115493, d142590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115494 q = 1) (hb : d142591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115494, d142591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115498 q = 1) (hb : d142593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115498, d142593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26341 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13803 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115499 q = 1) (hb : d142594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115499, d142594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115500 q = 1) (hb : d142595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115500, d142595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115501 q = 1) (hb : d142596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115501, d142596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115502 q = 1) (hb : d142597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115502, d142597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115508 q = 1) (hb : d142604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115508, d142604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26342 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13920 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115509 q = 1) (hb : d142605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115509, d142605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115510 q = 1) (hb : d142606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115510, d142606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115511 q = 1) (hb : d142607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115511, d142607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115512 q = 1) (hb : d142608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115512, d142608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115513 q = 1) (hb : d142609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115513, d142609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro26344 (p : Pattern) (ha : d115519 p = 1) (hb : d142615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d142610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d142610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26343 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d142611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d142611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d142612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d142612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d142613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d142613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d142614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d142614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d142615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d142615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26345 (p : Pattern) (ha : d115525 p = 1) (hb : d142621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d142502 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26314 q ha hb
    | true =>
      simp only [d115354, d142502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26320 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d142529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d142529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26326 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d142530 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d142530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d142557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d142557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26332 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d142558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d142558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d142559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d142559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d142586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d142586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26338 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d142587 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d142587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d142588 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d142588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d142589 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d142589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d142616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d142616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26344 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d142617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d142617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d142618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d142618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d142619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d142619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d142620 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d142620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d142621 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d142621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro26346 (p : Pattern) (ha : d115531 p = 1) (hb : d142627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d142622 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26345 q ha hb
    | true =>
      simp only [d115526, d142622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d142623 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d142623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d142624 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d142624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d142625 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d142625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d142626 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d142626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d142627 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d142627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26347 (p : Pattern) (ha : d115537 p = 1) (hb : d142633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d142628 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26346 q ha hb
    | true =>
      simp only [d115532, d142628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d142629 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d142629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d142630 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d142630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d142631 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d142631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d142632 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d142632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d142633 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d142633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26348 (p : Pattern) (ha : d115543 p = 1) (hb : d142639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d142634 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26347 q ha hb
    | true =>
      simp only [d115538, d142634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d142635 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d142635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d142636 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d142636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d142637 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d142637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d142638 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d142638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d142639 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d142639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26349 (p : Pattern) (ha : d115549 p = 1) (hb : d142645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d142640 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26348 q ha hb
    | true =>
      simp only [d115544, d142640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d142641 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d142641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115546 q = 1) (hb : d142642 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d142642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115547 q = 1) (hb : d142643 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d142643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115548 q = 1) (hb : d142644 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d142644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115549 q = 1) (hb : d142645 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d142645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26350 (p : Pattern) (ha : d115555 p = 1) (hb : d142651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d142646 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26349 q ha hb
    | true =>
      simp only [d115550, d142646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d142647 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d142647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d142648 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d142648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d142649 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d142649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d142650 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d142650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d142651 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d142651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26351 (p : Pattern) (ha : d115561 p = 1) (hb : d142657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d142652 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26350 q ha hb
    | true =>
      simp only [d115556, d142652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d142653 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d142653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d142654 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d142654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d142655 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d142655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d142656 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d142656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d142657 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d142657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26352 (p : Pattern) (ha : d115567 p = 1) (hb : d142663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d142658 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26351 q ha hb
    | true =>
      simp only [d115562, d142658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d142659 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d142659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d142660 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d142660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d142661 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d142661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d142662 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d142662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d142663 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d142663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26353 (p : Pattern) (ha : d30 p = 1) (hb : d142665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30 q = 1) (hb : d142665 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, d142665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d30, d142665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26354 (p : Pattern) (ha : d36 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26353 q ha hb
    | true =>
      simp only [d31, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d35 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26355 (p : Pattern) (ha : d42 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26356 (p : Pattern) (ha : d48 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26357 (p : Pattern) (ha : d49 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26358 (p : Pattern) (ha : d55 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26359 (p : Pattern) (ha : d60 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26360 (p : Pattern) (ha : d71 p = 1) (hb : d142665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71 q = 1) (hb : d142665 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, d142665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71, d142665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26361 (p : Pattern) (ha : d77 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d72 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26360 q ha hb
    | true =>
      simp only [d72, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d73 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26362 (p : Pattern) (ha : d83 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26361 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26363 (p : Pattern) (ha : d89 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26362 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26364 (p : Pattern) (ha : d95 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26356 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26358 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26359 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26363 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26365 (p : Pattern) (ha : d104 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26366 (p : Pattern) (ha : d111 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26367 (p : Pattern) (ha : d213 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26368 (p : Pattern) (ha : d116 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26369 (p : Pattern) (ha : d123 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26370 (p : Pattern) (ha : d144 p = 1) (hb : d142665 p = 1) : d120066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d143 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29 q = 1) (hb : d122304 q = 1) : d29 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144 q = 1) (hb : d142665 q = 1) : d120066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d142665, d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144, d142665, d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26371 (p : Pattern) (ha : d10654 p = 1) (hb : d142666 p = 1) : d120072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d142666 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26370 q ha hb
    | true =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d142666 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d142666 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26353 q ha hb
    | true =>
      simp only [d31, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d32 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10652 q = 1) (hb : d142666 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10652, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d34 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10653 q = 1) (hb : d142666 q = 1) : d120071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10653, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10654 q = 1) (hb : d142666 q = 1) : d120072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10654, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26372 (p : Pattern) (ha : d10660 p = 1) (hb : d142666 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10659 q = 1) (hb : d142666 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10659, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10660 q = 1) (hb : d142666 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10660, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26373 (p : Pattern) (ha : d108784 p = 1) (hb : d142666 p = 1) : d120084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26368 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26369 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10661 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26372 q ha hb
    | true =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
  have h9 (q : Pattern) (ha : d108780 q = 1) (hb : d142666 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108780, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108781 q = 1) (hb : d142666 q = 1) : d120081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108781, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108782 q = 1) (hb : d142666 q = 1) : d120082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108782, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108783 q = 1) (hb : d142666 q = 1) : d120083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108783, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108784 q = 1) (hb : d142666 q = 1) : d120084 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108784, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108784, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26374 (p : Pattern) (ha : d194 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26375 (p : Pattern) (ha : d199 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26376 (p : Pattern) (ha : d10667 p = 1) (hb : d142666 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10659 q = 1) (hb : d142666 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10659, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10667 q = 1) (hb : d142666 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10667, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26377 (p : Pattern) (ha : d108789 p = 1) (hb : d142666 p = 1) : d120091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26368 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26369 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10661 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26372 q ha hb
    | true =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
  have h9 (q : Pattern) (ha : d108780 q = 1) (hb : d142666 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108780, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108781 q = 1) (hb : d142666 q = 1) : d120081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108781, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108782 q = 1) (hb : d142666 q = 1) : d120082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108782, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108783 q = 1) (hb : d142666 q = 1) : d120083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108783, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26374 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26375 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10668 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26376 q ha hb
    | true =>
      simp only [d10668, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
  have h23 (q : Pattern) (ha : d108785 q = 1) (hb : d142666 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108785, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108786 q = 1) (hb : d142666 q = 1) : d120088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108786, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108787 q = 1) (hb : d142666 q = 1) : d120089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108787, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108787, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108788 q = 1) (hb : d142666 q = 1) : d120090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108788, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108788, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108789 q = 1) (hb : d142666 q = 1) : d120091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108789, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108789, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro26378 (p : Pattern) (ha : d108796 p = 1) (hb : d142666 p = 1) : d120096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10668 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26376 q ha hb
    | true =>
      simp only [d10668, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
  have h2 (q : Pattern) (ha : d108785 q = 1) (hb : d142666 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108785, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108786 q = 1) (hb : d142666 q = 1) : d120088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108786, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108794 q = 1) (hb : d142666 q = 1) : d120089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108794, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108794, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108795 q = 1) (hb : d142666 q = 1) : d120090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108795, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108795, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108796 q = 1) (hb : d142666 q = 1) : d120096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108796, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108796, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26379 (p : Pattern) (ha : d231 p = 1) (hb : d142665 p = 1) : d120102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d230 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70 q = 1) (hb : d122304 q = 1) : d70 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d231 q = 1) (hb : d142665 q = 1) : d120102 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d142665, d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d231, d142665, d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26380 (p : Pattern) (ha : d10691 p = 1) (hb : d142666 p = 1) : d120108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d142666 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26379 q ha hb
    | true =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d142666 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d142666 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26360 q ha hb
    | true =>
      simp only [d72, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d73 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10689 q = 1) (hb : d142666 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10689, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10690 q = 1) (hb : d142666 q = 1) : d120107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10690, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10691 q = 1) (hb : d142666 q = 1) : d120108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10691, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26381 (p : Pattern) (ha : d10697 p = 1) (hb : d142666 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d142666 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26380 q ha hb
    | true =>
      simp only [d10692, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d142666 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26361 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10694 q = 1) (hb : d142666 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10694, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10695 q = 1) (hb : d142666 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10695, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10696 q = 1) (hb : d142666 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10696, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10697 q = 1) (hb : d142666 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10697, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26382 (p : Pattern) (ha : d108806 p = 1) (hb : d142666 p = 1) : d120120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10698 q = 1) (hb : d142666 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26381 q ha hb
    | true =>
      simp only [d10698, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26362 q ha hb
  have h2 (q : Pattern) (ha : d108802 q = 1) (hb : d142666 q = 1) : d120116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108802, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108802, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26362 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108803 q = 1) (hb : d142666 q = 1) : d120117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108803, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108803, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108804 q = 1) (hb : d142666 q = 1) : d120118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108804, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108804, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108805 q = 1) (hb : d142666 q = 1) : d120119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108805, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108805, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108806 q = 1) (hb : d142666 q = 1) : d120120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108806, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108806, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26383 (p : Pattern) (ha : d108812 p = 1) (hb : d142666 p = 1) : d120126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26365 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26365 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26366 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108790 q = 1) (hb : d142666 q = 1) : d120092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108790, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26373 q ha hb
    | true =>
      simp only [d108790, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26377 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26367 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d108791 q = 1) (hb : d142666 q = 1) : d120093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108791, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108791, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108792 q = 1) (hb : d142666 q = 1) : d120094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108792, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108792, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108793 q = 1) (hb : d142666 q = 1) : d120095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108793, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108793, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108797 q = 1) (hb : d142666 q = 1) : d120097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108797, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108797, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26378 q ha hb
  have h12 (q : Pattern) (ha : d108798 q = 1) (hb : d142666 q = 1) : d120098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108798, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108798, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d108799 q = 1) (hb : d142666 q = 1) : d120099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108799, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108799, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108800 q = 1) (hb : d142666 q = 1) : d120100 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108800, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108800, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108801 q = 1) (hb : d142666 q = 1) : d120101 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108801, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108801, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108807 q = 1) (hb : d142666 q = 1) : d120121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108807, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108807, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26382 q ha hb
  have h17 (q : Pattern) (ha : d108808 q = 1) (hb : d142666 q = 1) : d120122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108808, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108808, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d108809 q = 1) (hb : d142666 q = 1) : d120123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108809, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108809, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d108810 q = 1) (hb : d142666 q = 1) : d120124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108810, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108810, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d108811 q = 1) (hb : d142666 q = 1) : d120125 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108811, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108811, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108812 q = 1) (hb : d142666 q = 1) : d120126 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108812, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108812, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro26384 (p : Pattern) (ha : d406 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26385 (p : Pattern) (ha : d462 p = 1) (hb : d142666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26362 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26386 (p : Pattern) (ha : d10719 p = 1) (hb : d142666 p = 1) : d120136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26372 q ha hb
    | true =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d142666 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d142666 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d142666 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d142666 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10719 q = 1) (hb : d142666 q = 1) : d120136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26387 (p : Pattern) (ha : d10726 p = 1) (hb : d142666 p = 1) : d120143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26372 q ha hb
    | true =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d142666 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d142666 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d142666 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d142666 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10668 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26376 q ha hb
    | true =>
      simp only [d10668, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
  have h7 (q : Pattern) (ha : d10722 q = 1) (hb : d142666 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10723 q = 1) (hb : d142666 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10723, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10724 q = 1) (hb : d142666 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10725 q = 1) (hb : d142666 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10726 q = 1) (hb : d142666 q = 1) : d120143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10726, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26388 (p : Pattern) (ha : d10801 p = 1) (hb : d142666 p = 1) : d120195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26372 q ha hb
    | true =>
      simp only [d10661, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d142666 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d142666 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d142666 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d142666 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26355 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10801 q = 1) (hb : d142666 q = 1) : d120195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10801, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26389 (p : Pattern) (ha : d10731 p = 1) (hb : d142666 p = 1) : d120148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10730 q = 1) (hb : d142666 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10731 q = 1) (hb : d142666 q = 1) : d120148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10731, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26390 (p : Pattern) (ha : d10738 p = 1) (hb : d142666 p = 1) : d120155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10736 q = 1) (hb : d142666 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10737 q = 1) (hb : d142666 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10737, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10738 q = 1) (hb : d142666 q = 1) : d120155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10738, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26391 (p : Pattern) (ha : d324 p = 1) (hb : d142665 p = 1) : d145277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d323 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d142 q = 1) : d142 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d143 q = 1) (hb : d122304 q = 1) : d13980 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d122304, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d143, d122304, d13980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d324 q = 1) (hb : d142665 q = 1) : d145277 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324, d142665, d145277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324, d142665, d145277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26392 (p : Pattern) (ha : d10747 p = 1) (hb : d142666 p = 1) : d145283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d142666 q = 1) : d145278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d142666, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26391 q ha hb
    | true =>
      simp only [d10742, d142666, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d142666 q = 1) : d145279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d142666 q = 1) : d145280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10649 q = 1) (hb : d142666 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26370 q ha hb
    | true =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10650 q = 1) (hb : d142666 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10651 q = 1) (hb : d142666 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10745 q = 1) (hb : d142666 q = 1) : d145281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26353 q ha hb
    | true =>
      simp only [d31, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d32 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10652 q = 1) (hb : d142666 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10652, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10746 q = 1) (hb : d142666 q = 1) : d145282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d145282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10746, d145282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10747 q = 1) (hb : d142666 q = 1) : d145283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d145283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10747, d145283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26393 (p : Pattern) (ha : d10753 p = 1) (hb : d142666 p = 1) : d145289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26392 q ha hb
    | true =>
      simp only [d10748, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d142666 q = 1) : d145286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d142666 q = 1) : d145287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d142666 q = 1) : d145288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10753 q = 1) (hb : d142666 q = 1) : d145289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d145289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10753, d145289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26394 (p : Pattern) (ha : d10772 p = 1) (hb : d142666 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d142666 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10772 q = 1) (hb : d142666 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10772, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26395 (p : Pattern) (ha : d108822 p = 1) (hb : d142666 p = 1) : d145295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10732 q = 1) (hb : d142666 q = 1) : d120149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26389 q ha hb
    | true =>
      simp only [d10732, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26368 q ha hb
  have h2 (q : Pattern) (ha : d10733 q = 1) (hb : d142666 q = 1) : d120150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10734 q = 1) (hb : d142666 q = 1) : d120151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10734, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10735 q = 1) (hb : d142666 q = 1) : d120152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10739 q = 1) (hb : d142666 q = 1) : d120156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26390 q ha hb
    | true =>
      simp only [d10739, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26369 q ha hb
  have h6 (q : Pattern) (ha : d10740 q = 1) (hb : d142666 q = 1) : d120157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10741 q = 1) (hb : d142666 q = 1) : d120158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10741, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10754 q = 1) (hb : d142666 q = 1) : d145290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26393 q ha hb
    | true =>
      simp only [d10754, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26372 q ha hb
  have h9 (q : Pattern) (ha : d108818 q = 1) (hb : d142666 q = 1) : d145291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d145291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108818, d145291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10773 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26394 q ha hb
    | true =>
      simp only [d10773, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10774 q = 1) (hb : d142666 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10774, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108819 q = 1) (hb : d142666 q = 1) : d145292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d145292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108819, d145292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108820 q = 1) (hb : d142666 q = 1) : d145293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d145293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108820, d145293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108821 q = 1) (hb : d142666 q = 1) : d145294 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d145294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108821, d145294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108822 q = 1) (hb : d142666 q = 1) : d145295 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d145295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108822, d145295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26396 (p : Pattern) (ha : d10779 p = 1) (hb : d142666 p = 1) : d120178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10730 q = 1) (hb : d142666 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10779 q = 1) (hb : d142666 q = 1) : d120178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10779, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26397 (p : Pattern) (ha : d10784 p = 1) (hb : d142666 p = 1) : d120183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26354 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10736 q = 1) (hb : d142666 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10737 q = 1) (hb : d142666 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10737, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10784 q = 1) (hb : d142666 q = 1) : d120183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10784, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26398 (p : Pattern) (ha : d10788 p = 1) (hb : d142666 p = 1) : d145296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26392 q ha hb
    | true =>
      simp only [d10748, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d142666 q = 1) : d145286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d142666 q = 1) : d145287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d142666 q = 1) : d145288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10788 q = 1) (hb : d142666 q = 1) : d145296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d145296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10788, d145296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26399 (p : Pattern) (ha : d10793 p = 1) (hb : d142666 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26371 q ha hb
    | true =>
      simp only [d10655, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d142666 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10793 q = 1) (hb : d142666 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10793, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26400 (p : Pattern) (ha : d108827 p = 1) (hb : d142666 p = 1) : d145302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10732 q = 1) (hb : d142666 q = 1) : d120149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26389 q ha hb
    | true =>
      simp only [d10732, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26368 q ha hb
  have h2 (q : Pattern) (ha : d10733 q = 1) (hb : d142666 q = 1) : d120150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10734 q = 1) (hb : d142666 q = 1) : d120151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10734, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10735 q = 1) (hb : d142666 q = 1) : d120152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10739 q = 1) (hb : d142666 q = 1) : d120156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26390 q ha hb
    | true =>
      simp only [d10739, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26369 q ha hb
  have h6 (q : Pattern) (ha : d10740 q = 1) (hb : d142666 q = 1) : d120157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10741 q = 1) (hb : d142666 q = 1) : d120158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10741, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10754 q = 1) (hb : d142666 q = 1) : d145290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26393 q ha hb
    | true =>
      simp only [d10754, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26372 q ha hb
  have h9 (q : Pattern) (ha : d108818 q = 1) (hb : d142666 q = 1) : d145291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d145291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108818, d145291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10773 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26394 q ha hb
    | true =>
      simp only [d10773, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10774 q = 1) (hb : d142666 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10774, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108819 q = 1) (hb : d142666 q = 1) : d145292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d145292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108819, d145292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108820 q = 1) (hb : d142666 q = 1) : d145293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d145293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108820, d145293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108821 q = 1) (hb : d142666 q = 1) : d145294 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d145294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108821, d145294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10780 q = 1) (hb : d142666 q = 1) : d120179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26396 q ha hb
    | true =>
      simp only [d10780, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26374 q ha hb
  have h16 (q : Pattern) (ha : d10781 q = 1) (hb : d142666 q = 1) : d120180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10781, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10782 q = 1) (hb : d142666 q = 1) : d120181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10782, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10783 q = 1) (hb : d142666 q = 1) : d120182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10783, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10785 q = 1) (hb : d142666 q = 1) : d120184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26397 q ha hb
    | true =>
      simp only [d10785, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26375 q ha hb
  have h20 (q : Pattern) (ha : d10786 q = 1) (hb : d142666 q = 1) : d120185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10786, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10787 q = 1) (hb : d142666 q = 1) : d120186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10787, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10789 q = 1) (hb : d142666 q = 1) : d145297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26398 q ha hb
    | true =>
      simp only [d10789, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26376 q ha hb
  have h23 (q : Pattern) (ha : d108823 q = 1) (hb : d142666 q = 1) : d145298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d145298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108823, d145298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10794 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26399 q ha hb
    | true =>
      simp only [d10794, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10795 q = 1) (hb : d142666 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10795, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108824 q = 1) (hb : d142666 q = 1) : d145299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d145299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108824, d145299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108825 q = 1) (hb : d142666 q = 1) : d145300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d145300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108825, d145300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108826 q = 1) (hb : d142666 q = 1) : d145301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d145301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108826, d145301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108827 q = 1) (hb : d142666 q = 1) : d145302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d145302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108827, d145302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro26401 (p : Pattern) (ha : d108834 p = 1) (hb : d142666 p = 1) : d145309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10789 q = 1) (hb : d142666 q = 1) : d145297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26398 q ha hb
    | true =>
      simp only [d10789, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26376 q ha hb
  have h2 (q : Pattern) (ha : d108823 q = 1) (hb : d142666 q = 1) : d145298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d145298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108823, d145298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10794 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26399 q ha hb
    | true =>
      simp only [d10794, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10795 q = 1) (hb : d142666 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10795, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108824 q = 1) (hb : d142666 q = 1) : d145299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d145299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108824, d145299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108832 q = 1) (hb : d142666 q = 1) : d145307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d145307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108832, d145307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108833 q = 1) (hb : d142666 q = 1) : d145308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d145308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108833, d145308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108834 q = 1) (hb : d142666 q = 1) : d145309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d145309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108834, d145309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26402 (p : Pattern) (ha : d417 p = 1) (hb : d142665 p = 1) : d145315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d229 q = 1) : d229 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d230 q = 1) (hb : d122304 q = 1) : d14019 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d122304, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d230, d122304, d14019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d417 q = 1) (hb : d142665 q = 1) : d145315 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d417, d142665, d145315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d417, d142665, d145315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26403 (p : Pattern) (ha : d10819 p = 1) (hb : d142666 p = 1) : d145321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d142666 q = 1) : d145316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d142666, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26402 q ha hb
    | true =>
      simp only [d10814, d142666, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d142666 q = 1) : d145317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d142666 q = 1) : d145318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10686 q = 1) (hb : d142666 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26379 q ha hb
    | true =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10687 q = 1) (hb : d142666 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10688 q = 1) (hb : d142666 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10817 q = 1) (hb : d142666 q = 1) : d145319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26360 q ha hb
    | true =>
      simp only [d72, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d73 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10689 q = 1) (hb : d142666 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10689, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10818 q = 1) (hb : d142666 q = 1) : d145320 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d145320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10818, d145320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10819 q = 1) (hb : d142666 q = 1) : d145321 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d145321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10819, d145321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26404 (p : Pattern) (ha : d10825 p = 1) (hb : d142666 p = 1) : d145327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10820 q = 1) (hb : d142666 q = 1) : d145322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26403 q ha hb
    | true =>
      simp only [d10820, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10821 q = 1) (hb : d142666 q = 1) : d145323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10821, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10692 q = 1) (hb : d142666 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26380 q ha hb
    | true =>
      simp only [d10692, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10693 q = 1) (hb : d142666 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10822 q = 1) (hb : d142666 q = 1) : d145324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d145324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10822, d145324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10823 q = 1) (hb : d142666 q = 1) : d145325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d145325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10823, d145325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10824 q = 1) (hb : d142666 q = 1) : d145326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d145326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10824, d145326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10825 q = 1) (hb : d142666 q = 1) : d145327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d145327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10825, d145327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26405 (p : Pattern) (ha : d10844 p = 1) (hb : d142666 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d142666 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26380 q ha hb
    | true =>
      simp only [d10692, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d142666 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10841 q = 1) (hb : d142666 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10841, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10842 q = 1) (hb : d142666 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10842, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10843 q = 1) (hb : d142666 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10843, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10844 q = 1) (hb : d142666 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10844, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26406 (p : Pattern) (ha : d108844 p = 1) (hb : d142666 p = 1) : d145333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10826 q = 1) (hb : d142666 q = 1) : d145328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d145328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26404 q ha hb
    | true =>
      simp only [d10826, d145328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26381 q ha hb
  have h2 (q : Pattern) (ha : d108840 q = 1) (hb : d142666 q = 1) : d145329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d145329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108840, d145329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10845 q = 1) (hb : d142666 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26405 q ha hb
    | true =>
      simp only [d10845, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10846 q = 1) (hb : d142666 q = 1) : d120116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10846, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108841 q = 1) (hb : d142666 q = 1) : d145330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d145330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108841, d145330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108842 q = 1) (hb : d142666 q = 1) : d145331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d145331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108842, d145331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108843 q = 1) (hb : d142666 q = 1) : d145332 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d145332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108843, d145332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108844 q = 1) (hb : d142666 q = 1) : d145333 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d145333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108844, d145333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26407 (p : Pattern) (ha : d108850 p = 1) (hb : d142666 p = 1) : d145339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10720 q = 1) (hb : d142666 q = 1) : d120137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10720, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26386 q ha hb
  have h2 (q : Pattern) (ha : d10721 q = 1) (hb : d142666 q = 1) : d120138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10721, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10727 q = 1) (hb : d142666 q = 1) : d120144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26386 q ha hb
    | true =>
      simp only [d10727, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26387 q ha hb
  have h4 (q : Pattern) (ha : d10728 q = 1) (hb : d142666 q = 1) : d120145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10728, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10729 q = 1) (hb : d142666 q = 1) : d120146 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10729, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108828 q = 1) (hb : d142666 q = 1) : d145303 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d145303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26395 q ha hb
    | true =>
      simp only [d108828, d145303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26400 q ha hb
  have h7 (q : Pattern) (ha : d10802 q = 1) (hb : d142666 q = 1) : d120196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26388 q ha hb
    | true =>
      simp only [d10802, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26366 q ha hb
  have h8 (q : Pattern) (ha : d108829 q = 1) (hb : d142666 q = 1) : d145304 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d145304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108829, d145304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108830 q = 1) (hb : d142666 q = 1) : d145305 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d145305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108830, d145305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108831 q = 1) (hb : d142666 q = 1) : d145306 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d145306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108831, d145306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108835 q = 1) (hb : d142666 q = 1) : d145310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d145310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108835, d145310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26401 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26384 q ha hb
  have h13 (q : Pattern) (ha : d108836 q = 1) (hb : d142666 q = 1) : d145311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d145311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108836, d145311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108837 q = 1) (hb : d142666 q = 1) : d145312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d145312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108837, d145312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108838 q = 1) (hb : d142666 q = 1) : d145313 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d145313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108838, d145313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108839 q = 1) (hb : d142666 q = 1) : d145314 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d145314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108839, d145314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108845 q = 1) (hb : d142666 q = 1) : d145334 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d145334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108845, d145334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26406 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26385 q ha hb
  have h19 (q : Pattern) (ha : d108846 q = 1) (hb : d142666 q = 1) : d145335 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d145335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108846, d145335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108847 q = 1) (hb : d142666 q = 1) : d145336 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d145336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108847, d145336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108848 q = 1) (hb : d142666 q = 1) : d145337 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d145337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108848, d145337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108849 q = 1) (hb : d142666 q = 1) : d145338 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d145338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108849, d145338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108850 q = 1) (hb : d142666 q = 1) : d145339 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d145339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108850, d145339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26408 (p : Pattern) (ha : d108856 p = 1) (hb : d142666 p = 1) : d145345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26364 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108813 q = 1) (hb : d142666 q = 1) : d120127 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108813, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108813, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26383 q ha hb
  have h6 (q : Pattern) (ha : d108814 q = 1) (hb : d142666 q = 1) : d120128 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108814, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108814, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108815 q = 1) (hb : d142666 q = 1) : d120129 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108815, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108815, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108816 q = 1) (hb : d142666 q = 1) : d120130 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108816, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108816, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108817 q = 1) (hb : d142666 q = 1) : d120131 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108817, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108817, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108851 q = 1) (hb : d142666 q = 1) : d145340 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d145340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108851, d145340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26407 q ha hb
  have h11 (q : Pattern) (ha : d108852 q = 1) (hb : d142666 q = 1) : d145341 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d145341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108852, d145341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108853 q = 1) (hb : d142666 q = 1) : d145342 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d145342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108853, d145342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108854 q = 1) (hb : d142666 q = 1) : d145343 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d145343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108854, d145343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108855 q = 1) (hb : d142666 q = 1) : d145344 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d145344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108855, d145344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108856 q = 1) (hb : d142666 q = 1) : d145345 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d145345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108856, d145345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26409 (p : Pattern) (ha : d10865 p = 1) (hb : d142666 p = 1) : d145283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d142666 q = 1) : d145278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d142666, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26391 q ha hb
    | true =>
      simp only [d10742, d142666, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d142666 q = 1) : d145279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d142666 q = 1) : d145280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10649 q = 1) (hb : d142666 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26370 q ha hb
    | true =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10650 q = 1) (hb : d142666 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10651 q = 1) (hb : d142666 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10745 q = 1) (hb : d142666 q = 1) : d145281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10863 q = 1) (hb : d142666 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10863, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10864 q = 1) (hb : d142666 q = 1) : d145282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d145282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10864, d145282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10865 q = 1) (hb : d142666 q = 1) : d145283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d145283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10865, d145283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26410 (p : Pattern) (ha : d10869 p = 1) (hb : d142666 p = 1) : d120072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d142666 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26370 q ha hb
    | true =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d142666 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d142666 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10863 q = 1) (hb : d142666 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10863, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10868 q = 1) (hb : d142666 q = 1) : d120071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10868, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10868, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10869 q = 1) (hb : d142666 q = 1) : d120072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10869, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10869, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26411 (p : Pattern) (ha : d10875 p = 1) (hb : d142666 p = 1) : d145289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d142666 q = 1) : d145286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d142666 q = 1) : d145287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d142666 q = 1) : d145288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10875 q = 1) (hb : d142666 q = 1) : d145289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d145289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10875, d145289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26412 (p : Pattern) (ha : d10879 p = 1) (hb : d142666 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d142666 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10879 q = 1) (hb : d142666 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10879, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10879, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26413 (p : Pattern) (ha : d10885 p = 1) (hb : d142666 p = 1) : d145350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d142666 q = 1) : d145290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26411 q ha hb
    | true =>
      simp only [d10880, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26412 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d142666 q = 1) : d145346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d142666 q = 1) : d145347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d142666 q = 1) : d145348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d142666 q = 1) : d145349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10885 q = 1) (hb : d142666 q = 1) : d145350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d145350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d145350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26414 (p : Pattern) (ha : d10888 p = 1) (hb : d142666 p = 1) : d145296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d142666 q = 1) : d145286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d142666 q = 1) : d145287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d142666 q = 1) : d145288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d145288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10888 q = 1) (hb : d142666 q = 1) : d145296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d145296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10888, d145296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26415 (p : Pattern) (ha : d10889 p = 1) (hb : d142666 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d142666 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10889 q = 1) (hb : d142666 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10889, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10889, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26416 (p : Pattern) (ha : d10895 p = 1) (hb : d142666 p = 1) : d145357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d142666 q = 1) : d145290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26411 q ha hb
    | true =>
      simp only [d10880, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26412 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d142666 q = 1) : d145346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d142666 q = 1) : d145347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d142666 q = 1) : d145348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d142666 q = 1) : d145349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10890 q = 1) (hb : d142666 q = 1) : d145297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26414 q ha hb
    | true =>
      simp only [d10890, d145297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26415 q ha hb
  have h7 (q : Pattern) (ha : d10891 q = 1) (hb : d142666 q = 1) : d145353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d145353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10892 q = 1) (hb : d142666 q = 1) : d145354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10892, d145354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10893 q = 1) (hb : d142666 q = 1) : d145355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d145355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10894 q = 1) (hb : d142666 q = 1) : d145356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d145356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10895 q = 1) (hb : d142666 q = 1) : d145357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d145357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10895, d145357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26417 (p : Pattern) (ha : d10992 p = 1) (hb : d142666 p = 1) : d145418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d142666 q = 1) : d145290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26411 q ha hb
    | true =>
      simp only [d10880, d145290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26412 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d142666 q = 1) : d145346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d145346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d142666 q = 1) : d145347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d145347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d142666 q = 1) : d145348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d145348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d142666 q = 1) : d145349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d145349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10987 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26412 q ha hb
    | true =>
      simp only [d10987, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10988 q = 1) (hb : d142666 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10989 q = 1) (hb : d142666 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10989, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10990 q = 1) (hb : d142666 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10991 q = 1) (hb : d142666 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10992 q = 1) (hb : d142666 q = 1) : d145418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d145418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10992, d145418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26418 (p : Pattern) (ha : d10998 p = 1) (hb : d142666 p = 1) : d120143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10987 q = 1) (hb : d142666 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26412 q ha hb
    | true =>
      simp only [d10987, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10988 q = 1) (hb : d142666 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10989 q = 1) (hb : d142666 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10989, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10990 q = 1) (hb : d142666 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10991 q = 1) (hb : d142666 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10993 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26415 q ha hb
    | true =>
      simp only [d10993, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10994 q = 1) (hb : d142666 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10995 q = 1) (hb : d142666 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10995, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10996 q = 1) (hb : d142666 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10997 q = 1) (hb : d142666 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10998 q = 1) (hb : d142666 q = 1) : d120143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10998, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10998, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26419 (p : Pattern) (ha : d11007 p = 1) (hb : d142666 p = 1) : d120334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10993 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26415 q ha hb
    | true =>
      simp only [d10993, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10994 q = 1) (hb : d142666 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10995 q = 1) (hb : d142666 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10995, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10996 q = 1) (hb : d142666 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10997 q = 1) (hb : d142666 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11007 q = 1) (hb : d142666 q = 1) : d120334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11007, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11007, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26420 (p : Pattern) (ha : d11031 p = 1) (hb : d142666 p = 1) : d120108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d142666 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26379 q ha hb
    | true =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d142666 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d142666 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11021 q = 1) (hb : d142666 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11021, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11030 q = 1) (hb : d142666 q = 1) : d120107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11030, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11030, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11031 q = 1) (hb : d142666 q = 1) : d120108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11031, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11031, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26421 (p : Pattern) (ha : d11076 p = 1) (hb : d142666 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11032 q = 1) (hb : d142666 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26420 q ha hb
    | true =>
      simp only [d11032, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11033 q = 1) (hb : d142666 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11073 q = 1) (hb : d142666 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11073, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11073, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11074 q = 1) (hb : d142666 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11074, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11074, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11075 q = 1) (hb : d142666 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11075, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11075, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11076 q = 1) (hb : d142666 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11076, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11076, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26422 (p : Pattern) (ha : d11082 p = 1) (hb : d142666 p = 1) : d120378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11077 q = 1) (hb : d142666 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11077, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26421 q ha hb
    | true =>
      simp only [d11077, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11078 q = 1) (hb : d142666 q = 1) : d120374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11078, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11078, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11079 q = 1) (hb : d142666 q = 1) : d120375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11079, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11079, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11080 q = 1) (hb : d142666 q = 1) : d120376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11080, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11080, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11081 q = 1) (hb : d142666 q = 1) : d120377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11081, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11081, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11082 q = 1) (hb : d142666 q = 1) : d120378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11082, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11082, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26423 (p : Pattern) (ha : d10900 p = 1) (hb : d142666 p = 1) : d145362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d142666 q = 1) : d145286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d142666 q = 1) : d145287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d142666 q = 1) : d145361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d145361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d145361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10900 q = 1) (hb : d142666 q = 1) : d145362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d145362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10900, d145362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26424 (p : Pattern) (ha : d10902 p = 1) (hb : d142666 p = 1) : d120148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d142666 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10902 q = 1) (hb : d142666 q = 1) : d120148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10902, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10902, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26425 (p : Pattern) (ha : d10909 p = 1) (hb : d142666 p = 1) : d145369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d142666 q = 1) : d145286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d142666 q = 1) : d145367 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d145367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d145367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d142666 q = 1) : d145368 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d145368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d145368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10909 q = 1) (hb : d142666 q = 1) : d145369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d145369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10909, d145369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26426 (p : Pattern) (ha : d10912 p = 1) (hb : d142666 p = 1) : d120155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d142666 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d142666 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d142666 q = 1) : d120155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10912, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10912, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26427 (p : Pattern) (ha : d548 p = 1) (hb : d142665 p = 1) : d145373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d547 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d322 q = 1) : d322 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d323 q = 1) (hb : d122304 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d323, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d548 q = 1) (hb : d142665 q = 1) : d145373 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d548, d142665, d145373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d548, d142665, d145373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26428 (p : Pattern) (ha : d10921 p = 1) (hb : d142666 p = 1) : d145379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10916 q = 1) (hb : d142666 q = 1) : d145374 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10916, d142666, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26427 q ha hb
    | true =>
      simp only [d10916, d142666, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10917 q = 1) (hb : d142666 q = 1) : d145375 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10917, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10917, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10918 q = 1) (hb : d142666 q = 1) : d145376 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10918, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10918, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10742 q = 1) (hb : d142666 q = 1) : d145278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d142666, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26391 q ha hb
    | true =>
      simp only [d10742, d142666, d145278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10743 q = 1) (hb : d142666 q = 1) : d145279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d145279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10744 q = 1) (hb : d142666 q = 1) : d145280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d145280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10919 q = 1) (hb : d142666 q = 1) : d145377 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d145377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10919, d145377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10649 q = 1) (hb : d142666 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26370 q ha hb
    | true =>
      simp only [d10649, d142666, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10650 q = 1) (hb : d142666 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10651 q = 1) (hb : d142666 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10745 q = 1) (hb : d142666 q = 1) : d145281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10745, d145281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10920 q = 1) (hb : d142666 q = 1) : d145378 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d145378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10920, d145378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10921 q = 1) (hb : d142666 q = 1) : d145379 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d145379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10921, d145379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26429 (p : Pattern) (ha : d10927 p = 1) (hb : d142666 p = 1) : d145385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d142666 q = 1) : d145380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d145380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26428 q ha hb
    | true =>
      simp only [d10922, d145380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d142666 q = 1) : d145381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d145381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d145381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d142666 q = 1) : d145382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d145382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d145382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d142666 q = 1) : d145383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d145383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d145383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d142666 q = 1) : d145384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d145384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d145384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10927 q = 1) (hb : d142666 q = 1) : d145385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d145385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10927, d145385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26430 (p : Pattern) (ha : d10955 p = 1) (hb : d142666 p = 1) : d145391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d142666 q = 1) : d145388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d145388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d145388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d142666 q = 1) : d145389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d145389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d145389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d142666 q = 1) : d145390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d145390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d145390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10955 q = 1) (hb : d142666 q = 1) : d145391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d145391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10955, d145391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26431 (p : Pattern) (ha : d108861 p = 1) (hb : d142666 p = 1) : d145397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d142666 q = 1) : d145363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d145363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26423 q ha hb
    | true =>
      simp only [d10903, d145363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26424 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d142666 q = 1) : d145364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d145364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d145364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d142666 q = 1) : d145365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d145365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d145365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d142666 q = 1) : d145366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d145366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d145366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d142666 q = 1) : d145370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d145370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26425 q ha hb
    | true =>
      simp only [d10913, d145370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26426 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d142666 q = 1) : d145371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d145371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d145371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d142666 q = 1) : d145372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d145372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d145372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d142666 q = 1) : d145386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d145386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26429 q ha hb
    | true =>
      simp only [d10928, d145386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26411 q ha hb
  have h9 (q : Pattern) (ha : d108857 q = 1) (hb : d142666 q = 1) : d145387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d145387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108857, d145387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10956 q = 1) (hb : d142666 q = 1) : d145392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d145392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26430 q ha hb
    | true =>
      simp only [d10956, d145392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10957 q = 1) (hb : d142666 q = 1) : d145393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d145393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10957, d145393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108858 q = 1) (hb : d142666 q = 1) : d145394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d145394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108858, d145394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108859 q = 1) (hb : d142666 q = 1) : d145395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d145395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108859, d145395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108860 q = 1) (hb : d142666 q = 1) : d145396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d145396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108860, d145396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108861 q = 1) (hb : d142666 q = 1) : d145397 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d145397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108861, d145397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26432 (p : Pattern) (ha : d10962 p = 1) (hb : d142666 p = 1) : d145398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d142666 q = 1) : d145286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d142666 q = 1) : d145287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d145287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d142666 q = 1) : d145361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d145361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d145361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10962 q = 1) (hb : d142666 q = 1) : d145398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d145398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10962, d145398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26433 (p : Pattern) (ha : d10963 p = 1) (hb : d142666 p = 1) : d120178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d142666 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d142666 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10963 q = 1) (hb : d142666 q = 1) : d120178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10963, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10963, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26434 (p : Pattern) (ha : d10968 p = 1) (hb : d142666 p = 1) : d145403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d142666 q = 1) : d145286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d145286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d142666 q = 1) : d145367 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d145367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d145367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d142666 q = 1) : d145368 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d145368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d145368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10968 q = 1) (hb : d142666 q = 1) : d145403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d145403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10968, d145403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26435 (p : Pattern) (ha : d10969 p = 1) (hb : d142666 p = 1) : d120183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d142666 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26410 q ha hb
    | true =>
      simp only [d10870, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d142666 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d142666 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d142666 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d142666 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10969 q = 1) (hb : d142666 q = 1) : d120183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10969, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10969, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26436 (p : Pattern) (ha : d10973 p = 1) (hb : d142666 p = 1) : d145407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d142666 q = 1) : d145380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d145380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26428 q ha hb
    | true =>
      simp only [d10922, d145380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d142666 q = 1) : d145381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d145381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d145381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d142666 q = 1) : d145382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d145382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d145382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d142666 q = 1) : d145383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d145383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d145383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d142666 q = 1) : d145384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d145384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d145384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10973 q = 1) (hb : d142666 q = 1) : d145407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d145407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10973, d145407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26437 (p : Pattern) (ha : d10979 p = 1) (hb : d142666 p = 1) : d145410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d142666 q = 1) : d145284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26409 q ha hb
    | true =>
      simp only [d10866, d145284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d142666 q = 1) : d145285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d145285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d142666 q = 1) : d145388 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d145388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d145388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d142666 q = 1) : d145389 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d145389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d145389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d142666 q = 1) : d145390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d145390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d145390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10979 q = 1) (hb : d142666 q = 1) : d145410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d145410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10979, d145410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26438 (p : Pattern) (ha : d108866 p = 1) (hb : d142666 p = 1) : d145416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d142666 q = 1) : d145363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d145363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26423 q ha hb
    | true =>
      simp only [d10903, d145363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26424 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d142666 q = 1) : d145364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d145364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d145364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d142666 q = 1) : d145365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d145365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d145365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d142666 q = 1) : d145366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d145366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d145366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d142666 q = 1) : d145370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d145370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26425 q ha hb
    | true =>
      simp only [d10913, d145370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26426 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d142666 q = 1) : d145371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d145371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d145371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d142666 q = 1) : d145372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d145372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d145372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d142666 q = 1) : d145386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d145386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26429 q ha hb
    | true =>
      simp only [d10928, d145386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26411 q ha hb
  have h9 (q : Pattern) (ha : d108857 q = 1) (hb : d142666 q = 1) : d145387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d145387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108857, d145387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10956 q = 1) (hb : d142666 q = 1) : d145392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d145392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26430 q ha hb
    | true =>
      simp only [d10956, d145392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10957 q = 1) (hb : d142666 q = 1) : d145393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d145393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10957, d145393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108858 q = 1) (hb : d142666 q = 1) : d145394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d145394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108858, d145394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108859 q = 1) (hb : d142666 q = 1) : d145395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d145395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108859, d145395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108860 q = 1) (hb : d142666 q = 1) : d145396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d145396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108860, d145396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10964 q = 1) (hb : d142666 q = 1) : d145399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d145399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26432 q ha hb
    | true =>
      simp only [d10964, d145399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26433 q ha hb
  have h16 (q : Pattern) (ha : d10965 q = 1) (hb : d142666 q = 1) : d145400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d145400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10965, d145400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10966 q = 1) (hb : d142666 q = 1) : d145401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d145401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10966, d145401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10967 q = 1) (hb : d142666 q = 1) : d145402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d145402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10967, d145402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10970 q = 1) (hb : d142666 q = 1) : d145404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d145404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26434 q ha hb
    | true =>
      simp only [d10970, d145404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26435 q ha hb
  have h20 (q : Pattern) (ha : d10971 q = 1) (hb : d142666 q = 1) : d145405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d145405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10971, d145405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10972 q = 1) (hb : d142666 q = 1) : d145406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d145406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10972, d145406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10974 q = 1) (hb : d142666 q = 1) : d145408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d145408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26436 q ha hb
    | true =>
      simp only [d10974, d145408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26414 q ha hb
  have h23 (q : Pattern) (ha : d108862 q = 1) (hb : d142666 q = 1) : d145409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d145409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108862, d145409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10980 q = 1) (hb : d142666 q = 1) : d145411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d145411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26437 q ha hb
    | true =>
      simp only [d10980, d145411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10981 q = 1) (hb : d142666 q = 1) : d145412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d145412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10981, d145412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108863 q = 1) (hb : d142666 q = 1) : d145413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d145413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108863, d145413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108864 q = 1) (hb : d142666 q = 1) : d145414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d145414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108864, d145414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108865 q = 1) (hb : d142666 q = 1) : d145415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d145415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108865, d145415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108866 q = 1) (hb : d142666 q = 1) : d145416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d145416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108866, d145416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro26439 (p : Pattern) (ha : d108873 p = 1) (hb : d142666 p = 1) : d145425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10974 q = 1) (hb : d142666 q = 1) : d145408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d145408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26436 q ha hb
    | true =>
      simp only [d10974, d145408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26414 q ha hb
  have h2 (q : Pattern) (ha : d108862 q = 1) (hb : d142666 q = 1) : d145409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d145409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108862, d145409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10980 q = 1) (hb : d142666 q = 1) : d145411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d145411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26437 q ha hb
    | true =>
      simp only [d10980, d145411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10981 q = 1) (hb : d142666 q = 1) : d145412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d145412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10981, d145412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108863 q = 1) (hb : d142666 q = 1) : d145413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d145413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108863, d145413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108871 q = 1) (hb : d142666 q = 1) : d145423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d145423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108871, d145423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108872 q = 1) (hb : d142666 q = 1) : d145424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d145424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108872, d145424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108873 q = 1) (hb : d142666 q = 1) : d145425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d145425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108873, d145425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26440 (p : Pattern) (ha : d664 p = 1) (hb : d142665 p = 1) : d145431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d415 q = 1) : d415 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d229 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d416 q = 1) (hb : d122304 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d416, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d664 q = 1) (hb : d142665 q = 1) : d145431 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d664, d142665, d145431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d664, d142665, d145431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26441 (p : Pattern) (ha : d11018 p = 1) (hb : d142666 p = 1) : d145437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11013 q = 1) (hb : d142666 q = 1) : d145432 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11013, d142666, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26440 q ha hb
    | true =>
      simp only [d11013, d142666, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11014 q = 1) (hb : d142666 q = 1) : d145433 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11014, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11014, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11015 q = 1) (hb : d142666 q = 1) : d145434 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11015, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11015, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10814 q = 1) (hb : d142666 q = 1) : d145316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d142666, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26402 q ha hb
    | true =>
      simp only [d10814, d142666, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10815 q = 1) (hb : d142666 q = 1) : d145317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10816 q = 1) (hb : d142666 q = 1) : d145318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11016 q = 1) (hb : d142666 q = 1) : d145435 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d145435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11016, d145435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10686 q = 1) (hb : d142666 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26379 q ha hb
    | true =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10687 q = 1) (hb : d142666 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10688 q = 1) (hb : d142666 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10817 q = 1) (hb : d142666 q = 1) : d145319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10817, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11017 q = 1) (hb : d142666 q = 1) : d145436 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d145436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11017, d145436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11018 q = 1) (hb : d142666 q = 1) : d145437 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d145437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11018, d145437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26442 (p : Pattern) (ha : d11023 p = 1) (hb : d142666 p = 1) : d145321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d142666 q = 1) : d145316 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d142666, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26402 q ha hb
    | true =>
      simp only [d10814, d142666, d145316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d142666 q = 1) : d145317 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d145317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d142666 q = 1) : d145318 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d145318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10686 q = 1) (hb : d142666 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26379 q ha hb
    | true =>
      simp only [d10686, d142666, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10687 q = 1) (hb : d142666 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10688 q = 1) (hb : d142666 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10817 q = 1) (hb : d142666 q = 1) : d145319 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d145319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11021 q = 1) (hb : d142666 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11021, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11022 q = 1) (hb : d142666 q = 1) : d145320 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d145320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11022, d145320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11023 q = 1) (hb : d142666 q = 1) : d145321 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d145321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11023, d145321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26443 (p : Pattern) (ha : d11029 p = 1) (hb : d142666 p = 1) : d145443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11019 q = 1) (hb : d142666 q = 1) : d145438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d145438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26441 q ha hb
    | true =>
      simp only [d11019, d145438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11020 q = 1) (hb : d142666 q = 1) : d145439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d145439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11020, d145439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11024 q = 1) (hb : d142666 q = 1) : d145322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26442 q ha hb
    | true =>
      simp only [d11024, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11025 q = 1) (hb : d142666 q = 1) : d145323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11026 q = 1) (hb : d142666 q = 1) : d145440 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d145440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11026, d145440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11027 q = 1) (hb : d142666 q = 1) : d145441 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d145441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11027, d145441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11028 q = 1) (hb : d142666 q = 1) : d145442 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d145442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11028, d145442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11029 q = 1) (hb : d142666 q = 1) : d145443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d145443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11029, d145443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26444 (p : Pattern) (ha : d11037 p = 1) (hb : d142666 p = 1) : d145327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d142666 q = 1) : d145322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26442 q ha hb
    | true =>
      simp only [d11024, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d142666 q = 1) : d145323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11032 q = 1) (hb : d142666 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26420 q ha hb
    | true =>
      simp only [d11032, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11033 q = 1) (hb : d142666 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11034 q = 1) (hb : d142666 q = 1) : d145324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d145324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11034, d145324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11035 q = 1) (hb : d142666 q = 1) : d145325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d145325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11035, d145325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11036 q = 1) (hb : d142666 q = 1) : d145326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d145326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11036, d145326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11037 q = 1) (hb : d142666 q = 1) : d145327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d145327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11037, d145327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26445 (p : Pattern) (ha : d11065 p = 1) (hb : d142666 p = 1) : d145449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d142666 q = 1) : d145322 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26442 q ha hb
    | true =>
      simp only [d11024, d145322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d142666 q = 1) : d145323 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d145323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11062 q = 1) (hb : d142666 q = 1) : d145446 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d145446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11062, d145446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11063 q = 1) (hb : d142666 q = 1) : d145447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d145447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11063, d145447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11064 q = 1) (hb : d142666 q = 1) : d145448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d145448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11064, d145448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11065 q = 1) (hb : d142666 q = 1) : d145449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d145449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11065, d145449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26446 (p : Pattern) (ha : d108883 p = 1) (hb : d142666 p = 1) : d145455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11038 q = 1) (hb : d142666 q = 1) : d145444 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d145444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26443 q ha hb
    | true =>
      simp only [d11038, d145444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26444 q ha hb
  have h2 (q : Pattern) (ha : d108879 q = 1) (hb : d142666 q = 1) : d145445 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d145445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108879, d145445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11066 q = 1) (hb : d142666 q = 1) : d145450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d145450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26445 q ha hb
    | true =>
      simp only [d11066, d145450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11067 q = 1) (hb : d142666 q = 1) : d145451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d145451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11067, d145451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108880 q = 1) (hb : d142666 q = 1) : d145452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d145452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108880, d145452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108881 q = 1) (hb : d142666 q = 1) : d145453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d145453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108881, d145453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108882 q = 1) (hb : d142666 q = 1) : d145454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d145454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108882, d145454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108883 q = 1) (hb : d142666 q = 1) : d145455 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d145455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108883, d145455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26447 (p : Pattern) (ha : d108889 p = 1) (hb : d142666 p = 1) : d145461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10886 q = 1) (hb : d142666 q = 1) : d145351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d145351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10886, d145351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26413 q ha hb
  have h2 (q : Pattern) (ha : d10887 q = 1) (hb : d142666 q = 1) : d145352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d145352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10887, d145352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10896 q = 1) (hb : d142666 q = 1) : d145358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d145358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26413 q ha hb
    | true =>
      simp only [d10896, d145358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26416 q ha hb
  have h4 (q : Pattern) (ha : d10897 q = 1) (hb : d142666 q = 1) : d145359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d145359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10897, d145359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10898 q = 1) (hb : d142666 q = 1) : d145360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d145360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10898, d145360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108867 q = 1) (hb : d142666 q = 1) : d145417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d145417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26431 q ha hb
    | true =>
      simp only [d108867, d145417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26438 q ha hb
  have h7 (q : Pattern) (ha : d10999 q = 1) (hb : d142666 q = 1) : d145419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d145419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26417 q ha hb
    | true =>
      simp only [d10999, d145419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26418 q ha hb
  have h8 (q : Pattern) (ha : d108868 q = 1) (hb : d142666 q = 1) : d145420 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d145420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108868, d145420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108869 q = 1) (hb : d142666 q = 1) : d145421 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d145421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108869, d145421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108870 q = 1) (hb : d142666 q = 1) : d145422 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d145422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108870, d145422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108874 q = 1) (hb : d142666 q = 1) : d145426 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d145426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108874, d145426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26439 q ha hb
  have h12 (q : Pattern) (ha : d11008 q = 1) (hb : d142666 q = 1) : d120335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11008, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26419 q ha hb
  have h13 (q : Pattern) (ha : d108875 q = 1) (hb : d142666 q = 1) : d145427 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d145427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108875, d145427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108876 q = 1) (hb : d142666 q = 1) : d145428 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d145428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108876, d145428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108877 q = 1) (hb : d142666 q = 1) : d145429 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d145429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108877, d145429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108878 q = 1) (hb : d142666 q = 1) : d145430 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d145430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108878, d145430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108884 q = 1) (hb : d142666 q = 1) : d145456 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d145456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108884, d145456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26446 q ha hb
  have h18 (q : Pattern) (ha : d11083 q = 1) (hb : d142666 q = 1) : d120379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11083, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26422 q ha hb
  have h19 (q : Pattern) (ha : d108885 q = 1) (hb : d142666 q = 1) : d145457 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d145457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108885, d145457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108886 q = 1) (hb : d142666 q = 1) : d145458 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d145458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108886, d145458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108887 q = 1) (hb : d142666 q = 1) : d145459 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d145459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108887, d145459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108888 q = 1) (hb : d142666 q = 1) : d145460 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d145460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108888, d145460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108889 q = 1) (hb : d142666 q = 1) : d145461 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d145461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108889, d145461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26448 (p : Pattern) (ha : d108895 p = 1) (hb : d142666 p = 1) : d145467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108890 q = 1) (hb : d142666 q = 1) : d145462 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d145462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108890, d145462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26447 q ha hb
  have h2 (q : Pattern) (ha : d108891 q = 1) (hb : d142666 q = 1) : d145463 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d145463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108891, d145463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108892 q = 1) (hb : d142666 q = 1) : d145464 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d145464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108892, d145464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108893 q = 1) (hb : d142666 q = 1) : d145465 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d145465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108893, d145465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108894 q = 1) (hb : d142666 q = 1) : d145466 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d145466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108894, d145466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108895 q = 1) (hb : d142666 q = 1) : d145467 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d145467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108895, d145467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26449 (p : Pattern) (ha : d756 p = 1) (hb : d142665 p = 1) : d145373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d547 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d322 q = 1) : d322 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d755 q = 1) (hb : d122304 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d755, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d756 q = 1) (hb : d142665 q = 1) : d145373 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d756, d142665, d145373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d756, d142665, d145373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26450 (p : Pattern) (ha : d758 p = 1) (hb : d142665 p = 1) : d120392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d757 q = 1) (hb : d122304 q = 1) : d757 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d758 q = 1) (hb : d142665 q = 1) : d120392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d142665, d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d758, d142665, d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26451 (p : Pattern) (ha : d11105 p = 1) (hb : d142666 p = 1) : d145471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d142666 q = 1) : d145374 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d142666, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26449 q ha hb
    | true =>
      simp only [d11096, d142666, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d142666 q = 1) : d145375 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d142666 q = 1) : d145376 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11099 q = 1) (hb : d142666 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26450 q ha hb
    | true =>
      simp only [d11099, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11100 q = 1) (hb : d142666 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11101 q = 1) (hb : d142666 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11102 q = 1) (hb : d142666 q = 1) : d145469 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11103 q = 1) (hb : d142666 q = 1) : d120400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11103, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11104 q = 1) (hb : d142666 q = 1) : d145470 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d145470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11104, d145470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11105 q = 1) (hb : d142666 q = 1) : d145471 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d145471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11105, d145471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26452 (p : Pattern) (ha : d11109 p = 1) (hb : d142666 p = 1) : d120406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11099 q = 1) (hb : d142666 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26450 q ha hb
    | true =>
      simp only [d11099, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11100 q = 1) (hb : d142666 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11101 q = 1) (hb : d142666 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11103 q = 1) (hb : d142666 q = 1) : d120400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11103, d120400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11108 q = 1) (hb : d142666 q = 1) : d120405 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11108, d120405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11108, d120405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11109 q = 1) (hb : d142666 q = 1) : d120406 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11109, d120406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11109, d120406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26453 (p : Pattern) (ha : d11115 p = 1) (hb : d142666 p = 1) : d145477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d142666 q = 1) : d145472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26451 q ha hb
    | true =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d142666 q = 1) : d145473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d142666 q = 1) : d145474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d142666 q = 1) : d145475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d142666 q = 1) : d145476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d145476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d145476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11115 q = 1) (hb : d142666 q = 1) : d145477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d145477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11115, d145477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26454 (p : Pattern) (ha : d11119 p = 1) (hb : d142666 p = 1) : d120416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d142666 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d142666 q = 1) : d120415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11119 q = 1) (hb : d142666 q = 1) : d120416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11119, d120416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11119, d120416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26455 (p : Pattern) (ha : d11125 p = 1) (hb : d142666 p = 1) : d145483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d142666 q = 1) : d145478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26453 q ha hb
    | true =>
      simp only [d11120, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26454 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d142666 q = 1) : d145479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d142666 q = 1) : d145480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d142666 q = 1) : d145481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d142666 q = 1) : d145482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11125 q = 1) (hb : d142666 q = 1) : d145483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d145483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d145483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26456 (p : Pattern) (ha : d11128 p = 1) (hb : d142666 p = 1) : d145486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d142666 q = 1) : d145472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26451 q ha hb
    | true =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d142666 q = 1) : d145473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d142666 q = 1) : d145474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d142666 q = 1) : d145475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d142666 q = 1) : d145476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d145476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d145476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11128 q = 1) (hb : d142666 q = 1) : d145486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d145486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11128, d145486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26457 (p : Pattern) (ha : d11129 p = 1) (hb : d142666 p = 1) : d120426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d142666 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d142666 q = 1) : d120415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11129 q = 1) (hb : d142666 q = 1) : d120426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11129, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11129, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26458 (p : Pattern) (ha : d11135 p = 1) (hb : d142666 p = 1) : d145492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d142666 q = 1) : d145478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26453 q ha hb
    | true =>
      simp only [d11120, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26454 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d142666 q = 1) : d145479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d142666 q = 1) : d145480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d142666 q = 1) : d145481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d142666 q = 1) : d145482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11130 q = 1) (hb : d142666 q = 1) : d145487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26456 q ha hb
    | true =>
      simp only [d11130, d145487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26457 q ha hb
  have h7 (q : Pattern) (ha : d11131 q = 1) (hb : d142666 q = 1) : d145488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d145488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11132 q = 1) (hb : d142666 q = 1) : d145489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11132, d145489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11133 q = 1) (hb : d142666 q = 1) : d145490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d145490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11134 q = 1) (hb : d142666 q = 1) : d145491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d145491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11135 q = 1) (hb : d142666 q = 1) : d145492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d145492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11135, d145492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26459 (p : Pattern) (ha : d11243 p = 1) (hb : d142666 p = 1) : d145562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d142666 q = 1) : d145478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26453 q ha hb
    | true =>
      simp only [d11120, d145478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26454 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d142666 q = 1) : d145479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d145479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d142666 q = 1) : d145480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d145480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d142666 q = 1) : d145481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d145481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d142666 q = 1) : d145482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d145482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11238 q = 1) (hb : d142666 q = 1) : d120514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26454 q ha hb
    | true =>
      simp only [d11238, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11239 q = 1) (hb : d142666 q = 1) : d120515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11240 q = 1) (hb : d142666 q = 1) : d120516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11240, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11241 q = 1) (hb : d142666 q = 1) : d120517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11242 q = 1) (hb : d142666 q = 1) : d120518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11243 q = 1) (hb : d142666 q = 1) : d145562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d145562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11243, d145562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26460 (p : Pattern) (ha : d11249 p = 1) (hb : d142666 p = 1) : d120525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11238 q = 1) (hb : d142666 q = 1) : d120514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26454 q ha hb
    | true =>
      simp only [d11238, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11239 q = 1) (hb : d142666 q = 1) : d120515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11240 q = 1) (hb : d142666 q = 1) : d120516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11240, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11241 q = 1) (hb : d142666 q = 1) : d120517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11242 q = 1) (hb : d142666 q = 1) : d120518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11244 q = 1) (hb : d142666 q = 1) : d120520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26457 q ha hb
    | true =>
      simp only [d11244, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11245 q = 1) (hb : d142666 q = 1) : d120521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11246 q = 1) (hb : d142666 q = 1) : d120522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11246, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11247 q = 1) (hb : d142666 q = 1) : d120523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11248 q = 1) (hb : d142666 q = 1) : d120524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11249 q = 1) (hb : d142666 q = 1) : d120525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11249, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11249, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26461 (p : Pattern) (ha : d11258 p = 1) (hb : d142666 p = 1) : d120534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11244 q = 1) (hb : d142666 q = 1) : d120520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26457 q ha hb
    | true =>
      simp only [d11244, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11245 q = 1) (hb : d142666 q = 1) : d120521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11246 q = 1) (hb : d142666 q = 1) : d120522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11246, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11247 q = 1) (hb : d142666 q = 1) : d120523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11248 q = 1) (hb : d142666 q = 1) : d120524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11258 q = 1) (hb : d142666 q = 1) : d120534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11258, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11258, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26462 (p : Pattern) (ha : d981 p = 1) (hb : d142665 p = 1) : d120545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d975 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d980 q = 1) (hb : d122304 q = 1) : d980 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d981 q = 1) (hb : d142665 q = 1) : d120545 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d142665, d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d981, d142665, d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26463 (p : Pattern) (ha : d11289 p = 1) (hb : d142666 p = 1) : d120567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11271 q = 1) (hb : d142666 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26462 q ha hb
    | true =>
      simp only [d11271, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11272 q = 1) (hb : d142666 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11273 q = 1) (hb : d142666 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11279 q = 1) (hb : d142666 q = 1) : d120565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11279, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11288 q = 1) (hb : d142666 q = 1) : d120566 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11288, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11288, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11289 q = 1) (hb : d142666 q = 1) : d120567 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11289, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11289, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro26464 (p : Pattern) (ha : d11345 p = 1) (hb : d142666 p = 1) : d120594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11290 q = 1) (hb : d142666 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26463 q ha hb
    | true =>
      simp only [d11290, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11291 q = 1) (hb : d142666 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11342 q = 1) (hb : d142666 q = 1) : d120591 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11342, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11342, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11343 q = 1) (hb : d142666 q = 1) : d120592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11343, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11343, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11344 q = 1) (hb : d142666 q = 1) : d120593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11344, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11344, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11345 q = 1) (hb : d142666 q = 1) : d120594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11345, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11345, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26465 (p : Pattern) (ha : d11351 p = 1) (hb : d142666 p = 1) : d120600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11346 q = 1) (hb : d142666 q = 1) : d120595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11346, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26464 q ha hb
    | true =>
      simp only [d11346, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11347 q = 1) (hb : d142666 q = 1) : d120596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11347, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11347, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11348 q = 1) (hb : d142666 q = 1) : d120597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11348, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11348, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11349 q = 1) (hb : d142666 q = 1) : d120598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11349, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11349, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11350 q = 1) (hb : d142666 q = 1) : d120599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11350, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11350, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11351 q = 1) (hb : d142666 q = 1) : d120600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11351, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11351, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26466 (p : Pattern) (ha : d11140 p = 1) (hb : d142666 p = 1) : d145497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d142666 q = 1) : d145472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26451 q ha hb
    | true =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d142666 q = 1) : d145473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d142666 q = 1) : d145474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d142666 q = 1) : d145475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d142666 q = 1) : d145496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d145496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d145496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11140 q = 1) (hb : d142666 q = 1) : d145497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d145497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11140, d145497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26467 (p : Pattern) (ha : d11142 p = 1) (hb : d142666 p = 1) : d120439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d142666 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d142666 q = 1) : d120438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11142 q = 1) (hb : d142666 q = 1) : d120439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11142, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11142, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26468 (p : Pattern) (ha : d11149 p = 1) (hb : d142666 p = 1) : d145504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d142666 q = 1) : d145472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26451 q ha hb
    | true =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d142666 q = 1) : d145473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d142666 q = 1) : d145474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d142666 q = 1) : d145502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d145502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d145502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d142666 q = 1) : d145503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d145503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d145503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11149 q = 1) (hb : d142666 q = 1) : d145504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d145504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11149, d145504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26469 (p : Pattern) (ha : d11152 p = 1) (hb : d142666 p = 1) : d120449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d142666 q = 1) : d120447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d142666 q = 1) : d120448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d142666 q = 1) : d120449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11152, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11152, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26470 (p : Pattern) (ha : d839 p = 1) (hb : d142665 p = 1) : d145508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d838 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d546 q = 1) : d546 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d547 q = 1) (hb : d122304 q = 1) : d14261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d122304, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d547, d122304, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d839 q = 1) (hb : d142665 q = 1) : d145508 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d839, d142665, d145508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d839, d142665, d145508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26471 (p : Pattern) (ha : d11161 p = 1) (hb : d142666 p = 1) : d145514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11156 q = 1) (hb : d142666 q = 1) : d145509 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11156, d142666, d145509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26470 q ha hb
    | true =>
      simp only [d11156, d142666, d145509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11157 q = 1) (hb : d142666 q = 1) : d145510 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11157, d145510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11157, d145510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11158 q = 1) (hb : d142666 q = 1) : d145511 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11158, d145511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11158, d145511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11096 q = 1) (hb : d142666 q = 1) : d145374 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d142666, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26449 q ha hb
    | true =>
      simp only [d11096, d142666, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11097 q = 1) (hb : d142666 q = 1) : d145375 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11098 q = 1) (hb : d142666 q = 1) : d145376 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11159 q = 1) (hb : d142666 q = 1) : d145512 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d145512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11159, d145512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11099 q = 1) (hb : d142666 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26450 q ha hb
    | true =>
      simp only [d11099, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11100 q = 1) (hb : d142666 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11101 q = 1) (hb : d142666 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11102 q = 1) (hb : d142666 q = 1) : d145469 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11102, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11160 q = 1) (hb : d142666 q = 1) : d145513 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d145513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11160, d145513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11161 q = 1) (hb : d142666 q = 1) : d145514 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d145514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11161, d145514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26472 (p : Pattern) (ha : d11167 p = 1) (hb : d142666 p = 1) : d145520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d142666 q = 1) : d145515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d145515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26471 q ha hb
    | true =>
      simp only [d11162, d145515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d142666 q = 1) : d145516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d145516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d145516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d142666 q = 1) : d145472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26451 q ha hb
    | true =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d142666 q = 1) : d145473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d142666 q = 1) : d145517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d145517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d145517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d142666 q = 1) : d145518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d145518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d145518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d142666 q = 1) : d145519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d145519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d145519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11167 q = 1) (hb : d142666 q = 1) : d145520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d145520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11167, d145520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26473 (p : Pattern) (ha : d5456 p = 1) (hb : d142665 p = 1) : d145523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5455 q = 1) (hb : d122304 q = 1) : d5455 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5456 q = 1) (hb : d142665 q = 1) : d145523 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5456, d142665, d145523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5456, d142665, d145523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26474 (p : Pattern) (ha : d11200 p = 1) (hb : d142666 p = 1) : d145529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d142666 q = 1) : d145374 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d142666, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26449 q ha hb
    | true =>
      simp only [d11096, d142666, d145374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d142666 q = 1) : d145375 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d145375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d142666 q = 1) : d145376 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d145376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11099 q = 1) (hb : d142666 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26450 q ha hb
    | true =>
      simp only [d11099, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11100 q = 1) (hb : d142666 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11101 q = 1) (hb : d142666 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11102 q = 1) (hb : d142666 q = 1) : d145469 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d145469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11195 q = 1) (hb : d142666 q = 1) : d145524 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11195, d142666, d145524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26473 q ha hb
    | true =>
      simp only [d11195, d142666, d145524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11196 q = 1) (hb : d142666 q = 1) : d145525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11196, d145525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11196, d145525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11197 q = 1) (hb : d142666 q = 1) : d145526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11197, d145526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11197, d145526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11198 q = 1) (hb : d142666 q = 1) : d145527 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11198, d145527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11198, d145527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11199 q = 1) (hb : d142666 q = 1) : d145528 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d145528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11199, d145528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11200 q = 1) (hb : d142666 q = 1) : d145529 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d145529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11200, d145529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26475 (p : Pattern) (ha : d11206 p = 1) (hb : d142666 p = 1) : d145535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d142666 q = 1) : d145530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d145530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26474 q ha hb
    | true =>
      simp only [d11201, d145530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d142666 q = 1) : d145531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d145531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d145531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d142666 q = 1) : d145532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d145532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d145532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d142666 q = 1) : d145533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d145533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d145533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d142666 q = 1) : d145534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d145534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d145534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11206 q = 1) (hb : d142666 q = 1) : d145535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d145535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11206, d145535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26476 (p : Pattern) (ha : d108901 p = 1) (hb : d142666 p = 1) : d145541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d142666 q = 1) : d145498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d145498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26466 q ha hb
    | true =>
      simp only [d11143, d145498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26467 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d142666 q = 1) : d145499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d145499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d145499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d142666 q = 1) : d145500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d145500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d145500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d142666 q = 1) : d145501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d145501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d145501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d142666 q = 1) : d145505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d145505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26468 q ha hb
    | true =>
      simp only [d11153, d145505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26469 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d142666 q = 1) : d145506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d145506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d145506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d142666 q = 1) : d145507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d145507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d145507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d142666 q = 1) : d145521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d145521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26472 q ha hb
    | true =>
      simp only [d11168, d145521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26453 q ha hb
  have h9 (q : Pattern) (ha : d108897 q = 1) (hb : d142666 q = 1) : d145522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d145522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108897, d145522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11207 q = 1) (hb : d142666 q = 1) : d145536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d145536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26475 q ha hb
    | true =>
      simp only [d11207, d145536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11208 q = 1) (hb : d142666 q = 1) : d145537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d145537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11208, d145537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108898 q = 1) (hb : d142666 q = 1) : d145538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d145538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108898, d145538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108899 q = 1) (hb : d142666 q = 1) : d145539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d145539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108899, d145539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108900 q = 1) (hb : d142666 q = 1) : d145540 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d145540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108900, d145540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108901 q = 1) (hb : d142666 q = 1) : d145541 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d145541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108901, d145541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26477 (p : Pattern) (ha : d11213 p = 1) (hb : d142666 p = 1) : d145542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d142666 q = 1) : d145472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26451 q ha hb
    | true =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d142666 q = 1) : d145473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d142666 q = 1) : d145474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d142666 q = 1) : d145475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d145475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d142666 q = 1) : d145496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d145496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d145496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11213 q = 1) (hb : d142666 q = 1) : d145542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d145542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11213, d145542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26478 (p : Pattern) (ha : d11214 p = 1) (hb : d142666 p = 1) : d120487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d142666 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d142666 q = 1) : d120438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11214 q = 1) (hb : d142666 q = 1) : d120487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11214, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11214, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26479 (p : Pattern) (ha : d11219 p = 1) (hb : d142666 p = 1) : d145547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d142666 q = 1) : d145472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26451 q ha hb
    | true =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d142666 q = 1) : d145473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d142666 q = 1) : d145474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d145474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d142666 q = 1) : d145502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d145502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d145502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d142666 q = 1) : d145503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d145503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d145503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11219 q = 1) (hb : d142666 q = 1) : d145547 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d145547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11219, d145547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26480 (p : Pattern) (ha : d11220 p = 1) (hb : d142666 p = 1) : d120493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26452 q ha hb
    | true =>
      simp only [d11110, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d142666 q = 1) : d120447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d142666 q = 1) : d120448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11220 q = 1) (hb : d142666 q = 1) : d120493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11220, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11220, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26481 (p : Pattern) (ha : d11224 p = 1) (hb : d142666 p = 1) : d145551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d142666 q = 1) : d145515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d145515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26471 q ha hb
    | true =>
      simp only [d11162, d145515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d142666 q = 1) : d145516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d145516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d145516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d142666 q = 1) : d145472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26451 q ha hb
    | true =>
      simp only [d11106, d145472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d142666 q = 1) : d145473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d145473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d142666 q = 1) : d145517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d145517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d145517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d142666 q = 1) : d145518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d145518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d145518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d142666 q = 1) : d145519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d145519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d145519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11224 q = 1) (hb : d142666 q = 1) : d145551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d145551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11224, d145551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26482 (p : Pattern) (ha : d11230 p = 1) (hb : d142666 p = 1) : d145554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d142666 q = 1) : d145530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d145530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26474 q ha hb
    | true =>
      simp only [d11201, d145530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d142666 q = 1) : d145531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d145531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d145531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d142666 q = 1) : d145532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d145532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d145532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d142666 q = 1) : d145533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d145533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d145533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d142666 q = 1) : d145534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d145534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d145534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11230 q = 1) (hb : d142666 q = 1) : d145554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11230, d145554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11230, d145554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26483 (p : Pattern) (ha : d108906 p = 1) (hb : d142666 p = 1) : d145560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d142666 q = 1) : d145498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d145498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26466 q ha hb
    | true =>
      simp only [d11143, d145498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26467 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d142666 q = 1) : d145499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d145499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d145499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d142666 q = 1) : d145500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d145500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d145500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d142666 q = 1) : d145501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d145501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d145501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d142666 q = 1) : d145505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d145505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26468 q ha hb
    | true =>
      simp only [d11153, d145505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26469 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d142666 q = 1) : d145506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d145506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d145506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d142666 q = 1) : d145507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d145507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d145507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d142666 q = 1) : d145521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d145521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26472 q ha hb
    | true =>
      simp only [d11168, d145521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26453 q ha hb
  have h9 (q : Pattern) (ha : d108897 q = 1) (hb : d142666 q = 1) : d145522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d145522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108897, d145522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11207 q = 1) (hb : d142666 q = 1) : d145536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d145536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26475 q ha hb
    | true =>
      simp only [d11207, d145536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11208 q = 1) (hb : d142666 q = 1) : d145537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d145537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11208, d145537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108898 q = 1) (hb : d142666 q = 1) : d145538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d145538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108898, d145538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108899 q = 1) (hb : d142666 q = 1) : d145539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d145539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108899, d145539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108900 q = 1) (hb : d142666 q = 1) : d145540 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d145540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108900, d145540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11215 q = 1) (hb : d142666 q = 1) : d145543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11215, d145543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26477 q ha hb
    | true =>
      simp only [d11215, d145543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26478 q ha hb
  have h16 (q : Pattern) (ha : d11216 q = 1) (hb : d142666 q = 1) : d145544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11216, d145544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11216, d145544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11217 q = 1) (hb : d142666 q = 1) : d145545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11217, d145545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11217, d145545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11218 q = 1) (hb : d142666 q = 1) : d145546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11218, d145546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11218, d145546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11221 q = 1) (hb : d142666 q = 1) : d145548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11221, d145548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26479 q ha hb
    | true =>
      simp only [d11221, d145548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26480 q ha hb
  have h20 (q : Pattern) (ha : d11222 q = 1) (hb : d142666 q = 1) : d145549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11222, d145549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11222, d145549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11223 q = 1) (hb : d142666 q = 1) : d145550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11223, d145550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11223, d145550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11225 q = 1) (hb : d142666 q = 1) : d145552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d145552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26481 q ha hb
    | true =>
      simp only [d11225, d145552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26456 q ha hb
  have h23 (q : Pattern) (ha : d108902 q = 1) (hb : d142666 q = 1) : d145553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d145553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108902, d145553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11231 q = 1) (hb : d142666 q = 1) : d145555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d145555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26482 q ha hb
    | true =>
      simp only [d11231, d145555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11232 q = 1) (hb : d142666 q = 1) : d145556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d145556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11232, d145556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108903 q = 1) (hb : d142666 q = 1) : d145557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d145557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108903, d145557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108904 q = 1) (hb : d142666 q = 1) : d145558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d145558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108904, d145558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108905 q = 1) (hb : d142666 q = 1) : d145559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d145559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108905, d145559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108906 q = 1) (hb : d142666 q = 1) : d145560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d145560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108906, d145560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro26484 (p : Pattern) (ha : d108913 p = 1) (hb : d142666 p = 1) : d145569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11225 q = 1) (hb : d142666 q = 1) : d145552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d145552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26481 q ha hb
    | true =>
      simp only [d11225, d145552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26456 q ha hb
  have h2 (q : Pattern) (ha : d108902 q = 1) (hb : d142666 q = 1) : d145553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d145553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108902, d145553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11231 q = 1) (hb : d142666 q = 1) : d145555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d145555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26482 q ha hb
    | true =>
      simp only [d11231, d145555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11232 q = 1) (hb : d142666 q = 1) : d145556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d145556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11232, d145556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108903 q = 1) (hb : d142666 q = 1) : d145557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d145557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108903, d145557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108911 q = 1) (hb : d142666 q = 1) : d145567 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d145567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108911, d145567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108912 q = 1) (hb : d142666 q = 1) : d145568 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d145568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108912, d145568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108913 q = 1) (hb : d142666 q = 1) : d145569 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d145569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108913, d145569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26485 (p : Pattern) (ha : d970 p = 1) (hb : d142665 p = 1) : d145575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d969 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d662 q = 1) : d662 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d415 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d663 q = 1) (hb : d122304 q = 1) : d14370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d122304, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d663, d122304, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d970 q = 1) (hb : d142665 q = 1) : d145575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d970, d142665, d145575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d970, d142665, d145575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26486 (p : Pattern) (ha : d976 p = 1) (hb : d142665 p = 1) : d145431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d415 q = 1) : d415 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d975 q = 1) (hb : d122304 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d975, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d976 q = 1) (hb : d142665 q = 1) : d145431 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d976, d142665, d145431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d976, d142665, d145431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26487 (p : Pattern) (ha : d11276 p = 1) (hb : d142666 p = 1) : d145582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11264 q = 1) (hb : d142666 q = 1) : d145576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11264, d142666, d145576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26485 q ha hb
    | true =>
      simp only [d11264, d142666, d145576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11265 q = 1) (hb : d142666 q = 1) : d145577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11265, d145577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11265, d145577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11266 q = 1) (hb : d142666 q = 1) : d145578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11266, d145578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11266, d145578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11267 q = 1) (hb : d142666 q = 1) : d145432 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d142666, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26486 q ha hb
    | true =>
      simp only [d11267, d142666, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11268 q = 1) (hb : d142666 q = 1) : d145433 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11269 q = 1) (hb : d142666 q = 1) : d145434 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11270 q = 1) (hb : d142666 q = 1) : d145579 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11270, d145579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11270, d145579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11271 q = 1) (hb : d142666 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26462 q ha hb
    | true =>
      simp only [d11271, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11272 q = 1) (hb : d142666 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11273 q = 1) (hb : d142666 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11274 q = 1) (hb : d142666 q = 1) : d145580 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11274, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11275 q = 1) (hb : d142666 q = 1) : d145581 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11275, d145581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11275, d145581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11276 q = 1) (hb : d142666 q = 1) : d145582 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11276, d145582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11276, d145582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26488 (p : Pattern) (ha : d11281 p = 1) (hb : d142666 p = 1) : d145586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d142666 q = 1) : d145432 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d142666, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26486 q ha hb
    | true =>
      simp only [d11267, d142666, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d142666 q = 1) : d145433 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d142666 q = 1) : d145434 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11271 q = 1) (hb : d142666 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26462 q ha hb
    | true =>
      simp only [d11271, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11272 q = 1) (hb : d142666 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11273 q = 1) (hb : d142666 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11274 q = 1) (hb : d142666 q = 1) : d145580 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11279 q = 1) (hb : d142666 q = 1) : d120565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11279, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11280 q = 1) (hb : d142666 q = 1) : d145585 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11280, d145585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11280, d145585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11281 q = 1) (hb : d142666 q = 1) : d145586 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11281, d145586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11281, d145586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro26489 (p : Pattern) (ha : d11287 p = 1) (hb : d142666 p = 1) : d145592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11277 q = 1) (hb : d142666 q = 1) : d145583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11277, d145583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26487 q ha hb
    | true =>
      simp only [d11277, d145583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11278 q = 1) (hb : d142666 q = 1) : d145584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11278, d145584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11278, d145584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11282 q = 1) (hb : d142666 q = 1) : d145587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d145587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26488 q ha hb
    | true =>
      simp only [d11282, d145587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11283 q = 1) (hb : d142666 q = 1) : d145588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d145588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d145588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11284 q = 1) (hb : d142666 q = 1) : d145589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11284, d145589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11284, d145589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11285 q = 1) (hb : d142666 q = 1) : d145590 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11285, d145590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11285, d145590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11286 q = 1) (hb : d142666 q = 1) : d145591 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11286, d145591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11286, d145591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11287 q = 1) (hb : d142666 q = 1) : d145592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11287, d145592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11287, d145592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26490 (p : Pattern) (ha : d11295 p = 1) (hb : d142666 p = 1) : d145596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11282 q = 1) (hb : d142666 q = 1) : d145587 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d145587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26488 q ha hb
    | true =>
      simp only [d11282, d145587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11283 q = 1) (hb : d142666 q = 1) : d145588 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d145588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d145588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11290 q = 1) (hb : d142666 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26463 q ha hb
    | true =>
      simp only [d11290, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11291 q = 1) (hb : d142666 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11292 q = 1) (hb : d142666 q = 1) : d145593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11292, d145593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11292, d145593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11293 q = 1) (hb : d142666 q = 1) : d145594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11293, d145594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11293, d145594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11294 q = 1) (hb : d142666 q = 1) : d145595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11294, d145595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11294, d145595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11295 q = 1) (hb : d142666 q = 1) : d145596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11295, d145596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11295, d145596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro26491 (p : Pattern) (ha : d5500 p = 1) (hb : d142665 p = 1) : d145599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d975 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5499 q = 1) (hb : d122304 q = 1) : d5499 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5500 q = 1) (hb : d142665 q = 1) : d145599 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5500, d142665, d145599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5500, d142665, d145599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26492 (p : Pattern) (ha : d11328 p = 1) (hb : d142666 p = 1) : d145605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d142666 q = 1) : d145432 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d142666, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26486 q ha hb
    | true =>
      simp only [d11267, d142666, d145432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d142666 q = 1) : d145433 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d145433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d142666 q = 1) : d145434 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d145434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11271 q = 1) (hb : d142666 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26462 q ha hb
    | true =>
      simp only [d11271, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11272 q = 1) (hb : d142666 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11273 q = 1) (hb : d142666 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11274 q = 1) (hb : d142666 q = 1) : d145580 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d145580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11323 q = 1) (hb : d142666 q = 1) : d145600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11323, d142666, d145600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26491 q ha hb
    | true =>
      simp only [d11323, d142666, d145600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11324 q = 1) (hb : d142666 q = 1) : d145601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11324, d145601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11324, d145601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11325 q = 1) (hb : d142666 q = 1) : d145602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11325, d145602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11325, d145602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11326 q = 1) (hb : d142666 q = 1) : d145603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11326, d145603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11326, d145603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11327 q = 1) (hb : d142666 q = 1) : d145604 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11327, d145604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11327, d145604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11328 q = 1) (hb : d142666 q = 1) : d145605 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11328, d145605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11328, d145605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro26493 (p : Pattern) (ha : d11334 p = 1) (hb : d142666 p = 1) : d145611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11329 q = 1) (hb : d142666 q = 1) : d145606 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11329, d145606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26492 q ha hb
    | true =>
      simp only [d11329, d145606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11330 q = 1) (hb : d142666 q = 1) : d145607 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11330, d145607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11330, d145607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11331 q = 1) (hb : d142666 q = 1) : d145608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11331, d145608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11331, d145608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11332 q = 1) (hb : d142666 q = 1) : d145609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11332, d145609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11332, d145609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11333 q = 1) (hb : d142666 q = 1) : d145610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11333, d145610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11333, d145610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11334 q = 1) (hb : d142666 q = 1) : d145611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11334, d145611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11334, d145611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro26494 (p : Pattern) (ha : d108923 p = 1) (hb : d142666 p = 1) : d145617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11296 q = 1) (hb : d142666 q = 1) : d145597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11296, d145597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26489 q ha hb
    | true =>
      simp only [d11296, d145597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26490 q ha hb
  have h2 (q : Pattern) (ha : d108919 q = 1) (hb : d142666 q = 1) : d145598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d145598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108919, d145598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11335 q = 1) (hb : d142666 q = 1) : d145612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11335, d145612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26493 q ha hb
    | true =>
      simp only [d11335, d145612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11336 q = 1) (hb : d142666 q = 1) : d145613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11336, d145613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11336, d145613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108920 q = 1) (hb : d142666 q = 1) : d145614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d145614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108920, d145614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108921 q = 1) (hb : d142666 q = 1) : d145615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d145615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108921, d145615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108922 q = 1) (hb : d142666 q = 1) : d145616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d145616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108922, d145616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108923 q = 1) (hb : d142666 q = 1) : d145617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d145617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108923, d145617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26495 (p : Pattern) (ha : d108929 p = 1) (hb : d142666 p = 1) : d145623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11126 q = 1) (hb : d142666 q = 1) : d145484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11126, d145484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11126, d145484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26455 q ha hb
  have h2 (q : Pattern) (ha : d11127 q = 1) (hb : d142666 q = 1) : d145485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11127, d145485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11127, d145485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11136 q = 1) (hb : d142666 q = 1) : d145493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d145493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26455 q ha hb
    | true =>
      simp only [d11136, d145493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26458 q ha hb
  have h4 (q : Pattern) (ha : d11137 q = 1) (hb : d142666 q = 1) : d145494 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d145494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11137, d145494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11138 q = 1) (hb : d142666 q = 1) : d145495 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11138, d145495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11138, d145495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108907 q = 1) (hb : d142666 q = 1) : d145561 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d145561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26476 q ha hb
    | true =>
      simp only [d108907, d145561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26483 q ha hb
  have h7 (q : Pattern) (ha : d11250 q = 1) (hb : d142666 q = 1) : d145563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11250, d145563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26459 q ha hb
    | true =>
      simp only [d11250, d145563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26460 q ha hb
  have h8 (q : Pattern) (ha : d108908 q = 1) (hb : d142666 q = 1) : d145564 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d145564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108908, d145564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108909 q = 1) (hb : d142666 q = 1) : d145565 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d145565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108909, d145565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108910 q = 1) (hb : d142666 q = 1) : d145566 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d145566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108910, d145566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108914 q = 1) (hb : d142666 q = 1) : d145570 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d145570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108914, d145570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26484 q ha hb
  have h12 (q : Pattern) (ha : d11259 q = 1) (hb : d142666 q = 1) : d120535 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11259, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11259, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26461 q ha hb
  have h13 (q : Pattern) (ha : d108915 q = 1) (hb : d142666 q = 1) : d145571 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d145571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108915, d145571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108916 q = 1) (hb : d142666 q = 1) : d145572 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d145572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108916, d145572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108917 q = 1) (hb : d142666 q = 1) : d145573 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d145573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108917, d145573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108918 q = 1) (hb : d142666 q = 1) : d145574 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d145574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108918, d145574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108924 q = 1) (hb : d142666 q = 1) : d145618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d145618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108924, d145618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26494 q ha hb
  have h18 (q : Pattern) (ha : d11352 q = 1) (hb : d142666 q = 1) : d120601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11352, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11352, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26465 q ha hb
  have h19 (q : Pattern) (ha : d108925 q = 1) (hb : d142666 q = 1) : d145619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d145619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108925, d145619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108926 q = 1) (hb : d142666 q = 1) : d145620 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d145620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108926, d145620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108927 q = 1) (hb : d142666 q = 1) : d145621 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d145621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108927, d145621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108928 q = 1) (hb : d142666 q = 1) : d145622 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d145622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108928, d145622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108929 q = 1) (hb : d142666 q = 1) : d145623 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d145623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108929, d145623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26496 (p : Pattern) (ha : d108935 p = 1) (hb : d142666 p = 1) : d145629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108930 q = 1) (hb : d142666 q = 1) : d145624 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d145624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108930, d145624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26495 q ha hb
  have h2 (q : Pattern) (ha : d108931 q = 1) (hb : d142666 q = 1) : d145625 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d145625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108931, d145625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108932 q = 1) (hb : d142666 q = 1) : d145626 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d145626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108932, d145626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108933 q = 1) (hb : d142666 q = 1) : d145627 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d145627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108933, d145627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108934 q = 1) (hb : d142666 q = 1) : d145628 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d145628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108934, d145628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108935 q = 1) (hb : d142666 q = 1) : d145629 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d145629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108935, d145629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26497 (p : Pattern) (ha : d1126 p = 1) (hb : d142665 p = 1) : d145632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1113 q = 1) : d1113 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1125 q = 1) (hb : d122304 q = 1) : d14762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d122304, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1125, d122304, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1126 q = 1) (hb : d142665 q = 1) : d145632 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1126, d142665, d145632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1126, d142665, d145632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro26498 (p : Pattern) (ha : d1128 p = 1) (hb : d142665 p = 1) : d145636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1127 q = 1) (hb : d122304 q = 1) : d1127 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1128 q = 1) (hb : d142665 q = 1) : d145636 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1128, d142665, d145636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1128, d142665, d145636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro26499 (p : Pattern) (ha : d11375 p = 1) (hb : d142666 p = 1) : d145643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d142666 q = 1) : d145633 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d142666, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26497 q ha hb
    | true =>
      simp only [d11366, d142666, d145633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d142666 q = 1) : d145634 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d145634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d142666 q = 1) : d145635 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d145635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11369 q = 1) (hb : d142666 q = 1) : d145637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d142666, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26498 q ha hb
    | true =>
      simp only [d11369, d142666, d145637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11370 q = 1) (hb : d142666 q = 1) : d145638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d145638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11371 q = 1) (hb : d142666 q = 1) : d145639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d145639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11372 q = 1) (hb : d142666 q = 1) : d145640 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d145640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11373 q = 1) (hb : d142666 q = 1) : d145641 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d145641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11373, d145641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11374 q = 1) (hb : d142666 q = 1) : d145642 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11374, d145642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11374, d145642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11375 q = 1) (hb : d142666 q = 1) : d145643 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11375, d145643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11375, d145643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
end NetHack.Soko22Hazard87
