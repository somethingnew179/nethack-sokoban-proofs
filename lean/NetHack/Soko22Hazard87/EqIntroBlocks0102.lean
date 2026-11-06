import NetHack.Soko22Hazard87.EqIntroBlocks0101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro25500 (p : Pattern) (selected : d246520 p = 0) : d247908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246377 q = 0) : d247808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246377, d247808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25464 q selected
    | true =>
      simp only [d246377, d247808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25465 q selected
  have h2 (q : Pattern) (selected : d246378 q = 0) : d247809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246378, d247809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246378, d247809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246379 q = 0) : d247810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246379, d247810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246379, d247810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246380 q = 0) : d247811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246380, d247811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246380, d247811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246381 q = 0) : d247812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246381, d247812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246381, d247812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246515 q = 0) : d247903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246515, d247903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25465 q selected
    | true =>
      simp only [d246515, d247903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246516 q = 0) : d247904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246516, d247904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246516, d247904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246517 q = 0) : d247905 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246517, d247905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246517, d247905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246518 q = 0) : d247906 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246518, d247906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246518, d247906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246519 q = 0) : d247907 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246519, d247907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246519, d247907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246520 q = 0) : d247908 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246520, d247908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246520, d247908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro25501 (p : Pattern) (selected : d246526 p = 0) : d247914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246515 q = 0) : d247903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246515, d247903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25465 q selected
    | true =>
      simp only [d246515, d247903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246516 q = 0) : d247904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246516, d247904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246516, d247904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246517 q = 0) : d247905 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246517, d247905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246517, d247905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246518 q = 0) : d247906 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246518, d247906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246518, d247906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246519 q = 0) : d247907 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246519, d247907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246519, d247907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246521 q = 0) : d247909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246521, d247909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25468 q selected
    | true =>
      simp only [d246521, d247909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246522 q = 0) : d247910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246522, d247910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246522, d247910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246523 q = 0) : d247911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246523, d247911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246523, d247911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246524 q = 0) : d247912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246524, d247912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246524, d247912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246525 q = 0) : d247913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246525, d247913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246525, d247913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246526 q = 0) : d247914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246526, d247914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246526, d247914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro25502 (p : Pattern) (selected : d246533 p = 0) : d247921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246502 q = 0) : d247893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246502, d247893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25495 q selected
    | true =>
      simp only [d246502, d247893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25467 q selected
  have h2 (q : Pattern) (selected : d246505 q = 0) : d247818 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246505, d247818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25496 q selected
    | true =>
      simp only [d246505, d247818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25497 q selected
  have h3 (q : Pattern) (selected : d246506 q = 0) : d247894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246506, d247894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246506, d247894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246508 q = 0) : d247896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246508, d247896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25498 q selected
    | true =>
      simp only [d246508, d247896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246509 q = 0) : d247897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246509, d247897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246509, d247897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246510 q = 0) : d247898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246510, d247898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246510, d247898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246531 q = 0) : d247919 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246531, d247919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246531, d247919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246532 q = 0) : d247920 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246532, d247920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246532, d247920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246533 q = 0) : d247921 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246533, d247921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246533, d247921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25503 (p : Pattern) (selected : d246535 p = 0) : d247923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246521 q = 0) : d247909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246521, d247909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25468 q selected
    | true =>
      simp only [d246521, d247909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246522 q = 0) : d247910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246522, d247910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246522, d247910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246523 q = 0) : d247911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246523, d247911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246523, d247911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246524 q = 0) : d247912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246524, d247912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246524, d247912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246525 q = 0) : d247913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246525, d247913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246525, d247913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246535 q = 0) : d247923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246535, d247923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246535, d247923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25504 (p : Pattern) (selected : d246549 p = 0) : d247937 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246541 q = 0) : d247929 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246541, d247929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246541, d247929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25474 q selected
  have h2 (q : Pattern) (selected : d246413 q = 0) : d247844 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246413, d247844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25474 q selected
    | true =>
      simp only [d246413, d247844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246542 q = 0) : d247930 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246542, d247930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246542, d247930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246414 q = 0) : d247845 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246414, d247845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246414, d247845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246543 q = 0) : d247931 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246543, d247931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246543, d247931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246544 q = 0) : d247932 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246544, d247932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246544, d247932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246545 q = 0) : d247933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246545, d247933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246545, d247933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25456 q selected
  have h8 (q : Pattern) (selected : d246338 q = 0) : d247769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246338, d247769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25456 q selected
    | true =>
      simp only [d246338, d247769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246546 q = 0) : d247934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246546, d247934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246546, d247934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246339 q = 0) : d247770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246339, d247770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246339, d247770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d246547 q = 0) : d247935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246547, d247935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246547, d247935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246548 q = 0) : d247936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246548, d247936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246548, d247936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246549 q = 0) : d247937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246549, d247937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246549, d247937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25505 (p : Pattern) (selected : d246554 p = 0) : d247942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246545 q = 0) : d247933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246545, d247933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246545, d247933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25456 q selected
  have h2 (q : Pattern) (selected : d246338 q = 0) : d247769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246338, d247769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25456 q selected
    | true =>
      simp only [d246338, d247769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246546 q = 0) : d247934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246546, d247934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246546, d247934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246339 q = 0) : d247770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246339, d247770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246339, d247770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246547 q = 0) : d247935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246547, d247935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246547, d247935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246548 q = 0) : d247936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246548, d247936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246548, d247936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246550 q = 0) : d247938 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246550, d247938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246550, d247938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25457 q selected
  have h8 (q : Pattern) (selected : d246342 q = 0) : d247773 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246342, d247773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25457 q selected
    | true =>
      simp only [d246342, d247773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246551 q = 0) : d247939 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246551, d247939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246551, d247939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246343 q = 0) : d247774 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246343, d247774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246343, d247774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d246552 q = 0) : d247940 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246552, d247940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246552, d247940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246553 q = 0) : d247941 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246553, d247941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246553, d247941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246554 q = 0) : d247942 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246554, d247942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246554, d247942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25506 (p : Pattern) (selected : d246558 p = 0) : d247946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246550 q = 0) : d247938 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246550, d247938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246550, d247938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25457 q selected
  have h2 (q : Pattern) (selected : d246342 q = 0) : d247773 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246342, d247773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25457 q selected
    | true =>
      simp only [d246342, d247773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246551 q = 0) : d247939 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246551, d247939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246551, d247939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246343 q = 0) : d247774 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246343, d247774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246343, d247774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246552 q = 0) : d247940 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246552, d247940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246552, d247940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246553 q = 0) : d247941 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246553, d247941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246553, d247941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246558 q = 0) : d247946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246558, d247946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246558, d247946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25507 (p : Pattern) (selected : d246567 p = 0) : d247955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246563 q = 0) : d247951 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246563, d247951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246563, d247951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25460 q selected
  have h2 (q : Pattern) (selected : d246351 q = 0) : d247782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246351, d247782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25460 q selected
    | true =>
      simp only [d246351, d247782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246564 q = 0) : d247952 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246564, d247952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246564, d247952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246352 q = 0) : d247783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246352, d247783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246352, d247783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246565 q = 0) : d247953 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246565, d247953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246565, d247953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246566 q = 0) : d247954 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246566, d247954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246566, d247954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246567 q = 0) : d247955 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246567, d247955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246567, d247955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25508 (p : Pattern) (selected : d246573 p = 0) : d247961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246555 q = 0) : d247943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246555, d247943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25504 q selected
    | true =>
      simp only [d246555, d247943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25505 q selected
  have h2 (q : Pattern) (selected : d246556 q = 0) : d247944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246556, d247944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246556, d247944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246557 q = 0) : d247945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246557, d247945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246557, d247945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246559 q = 0) : d247947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246559, d247947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25505 q selected
    | true =>
      simp only [d246559, d247947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25506 q selected
  have h5 (q : Pattern) (selected : d246560 q = 0) : d247948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246560, d247948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246560, d247948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246561 q = 0) : d247949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246561, d247949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246561, d247949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246562 q = 0) : d247950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246562, d247950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246562, d247950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246568 q = 0) : d247956 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246568, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25506 q selected
    | true =>
      simp only [d246568, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25507 q selected
  have h9 (q : Pattern) (selected : d246569 q = 0) : d247957 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246569, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246569, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246570 q = 0) : d247958 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246570, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246570, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246571 q = 0) : d247959 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246571, d247959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246571, d247959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246572 q = 0) : d247960 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246572, d247960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246572, d247960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246573 q = 0) : d247961 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246573, d247961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246573, d247961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25509 (p : Pattern) (selected : d246578 p = 0) : d247966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246559 q = 0) : d247947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246559, d247947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25505 q selected
    | true =>
      simp only [d246559, d247947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25506 q selected
  have h2 (q : Pattern) (selected : d246560 q = 0) : d247948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246560, d247948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246560, d247948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246561 q = 0) : d247949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246561, d247949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246561, d247949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246568 q = 0) : d247956 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246568, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25506 q selected
    | true =>
      simp only [d246568, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25507 q selected
  have h5 (q : Pattern) (selected : d246569 q = 0) : d247957 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246569, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246569, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246570 q = 0) : d247958 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246570, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246570, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246571 q = 0) : d247959 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246571, d247959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246571, d247959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246576 q = 0) : d247964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246576, d247964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246576, d247964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246577 q = 0) : d247965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246577, d247965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246577, d247965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246578 q = 0) : d247966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246578, d247966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246578, d247966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25510 (p : Pattern) (selected : d246584 p = 0) : d247972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246574 q = 0) : d247962 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246574, d247962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25508 q selected
    | true =>
      simp only [d246574, d247962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246575 q = 0) : d247963 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246575, d247963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246575, d247963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246579 q = 0) : d247967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246579, d247967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25509 q selected
    | true =>
      simp only [d246579, d247967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246580 q = 0) : d247968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246580, d247968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246580, d247968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246581 q = 0) : d247969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246581, d247969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246581, d247969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246582 q = 0) : d247970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246582, d247970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246582, d247970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246583 q = 0) : d247971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246583, d247971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246583, d247971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246584 q = 0) : d247972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246584, d247972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246584, d247972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25511 (p : Pattern) (selected : d246586 p = 0) : d247974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246568 q = 0) : d247956 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246568, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25506 q selected
    | true =>
      simp only [d246568, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25507 q selected
  have h2 (q : Pattern) (selected : d246569 q = 0) : d247957 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246569, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246569, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246570 q = 0) : d247958 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246570, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246570, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246576 q = 0) : d247964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246576, d247964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246576, d247964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246585 q = 0) : d247973 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246585, d247973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246585, d247973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246586 q = 0) : d247974 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246586, d247974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246586, d247974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25512 (p : Pattern) (selected : d246592 p = 0) : d247980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246579 q = 0) : d247967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246579, d247967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25509 q selected
    | true =>
      simp only [d246579, d247967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246580 q = 0) : d247968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246580, d247968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246580, d247968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246587 q = 0) : d247975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246587, d247975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25511 q selected
    | true =>
      simp only [d246587, d247975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246588 q = 0) : d247976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246588, d247976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246588, d247976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246589 q = 0) : d247977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246589, d247977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246589, d247977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246590 q = 0) : d247978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246590, d247978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246590, d247978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246591 q = 0) : d247979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246591, d247979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246591, d247979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246592 q = 0) : d247980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246592, d247980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246592, d247980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25513 (p : Pattern) (selected : d246602 p = 0) : d247942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246594 q = 0) : d247933 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246594, d247933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246594, d247933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25478 q selected
  have h2 (q : Pattern) (selected : d246431 q = 0) : d247769 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246431, d247769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25478 q selected
    | true =>
      simp only [d246431, d247769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246595 q = 0) : d247934 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246595, d247934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246595, d247934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246432 q = 0) : d247770 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246432, d247770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246432, d247770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246596 q = 0) : d247935 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246596, d247935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246596, d247935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246597 q = 0) : d247936 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246597, d247936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246597, d247936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246598 q = 0) : d247938 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246598, d247938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246598, d247938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25479 q selected
  have h8 (q : Pattern) (selected : d246435 q = 0) : d247773 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246435, d247773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25479 q selected
    | true =>
      simp only [d246435, d247773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246599 q = 0) : d247939 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246599, d247939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246599, d247939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246436 q = 0) : d247774 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246436, d247774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246436, d247774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d246600 q = 0) : d247940 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246600, d247940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246600, d247940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246601 q = 0) : d247941 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246601, d247941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246601, d247941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246602 q = 0) : d247942 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246602, d247942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246602, d247942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25514 (p : Pattern) (selected : d246603 p = 0) : d247946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246598 q = 0) : d247938 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246598, d247938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246598, d247938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25479 q selected
  have h2 (q : Pattern) (selected : d246435 q = 0) : d247773 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246435, d247773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25479 q selected
    | true =>
      simp only [d246435, d247773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246599 q = 0) : d247939 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246599, d247939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246599, d247939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246436 q = 0) : d247774 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246436, d247774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246436, d247774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246600 q = 0) : d247940 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246600, d247940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246600, d247940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246601 q = 0) : d247941 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246601, d247941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246601, d247941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246603 q = 0) : d247946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246603, d247946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246603, d247946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25515 (p : Pattern) (selected : d246611 p = 0) : d247955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246607 q = 0) : d247951 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246607, d247951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246607, d247951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25482 q selected
  have h2 (q : Pattern) (selected : d246444 q = 0) : d247782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246444, d247782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25482 q selected
    | true =>
      simp only [d246444, d247782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246608 q = 0) : d247952 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246608, d247952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246608, d247952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246445 q = 0) : d247783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246445, d247783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246445, d247783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246609 q = 0) : d247953 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246609, d247953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246609, d247953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246610 q = 0) : d247954 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246610, d247954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246610, d247954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246611 q = 0) : d247955 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246611, d247955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246611, d247955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25516 (p : Pattern) (selected : d246618 p = 0) : d247966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246604 q = 0) : d247947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246604, d247947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25513 q selected
    | true =>
      simp only [d246604, d247947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25514 q selected
  have h2 (q : Pattern) (selected : d246605 q = 0) : d247948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246605, d247948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246605, d247948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246606 q = 0) : d247949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246606, d247949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246606, d247949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246612 q = 0) : d247956 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246612, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25514 q selected
    | true =>
      simp only [d246612, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25515 q selected
  have h5 (q : Pattern) (selected : d246613 q = 0) : d247957 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246613, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246613, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246614 q = 0) : d247958 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246614, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246614, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246615 q = 0) : d247959 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246615, d247959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246615, d247959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246616 q = 0) : d247964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246616, d247964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246616, d247964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246617 q = 0) : d247965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246617, d247965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246617, d247965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246618 q = 0) : d247966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246618, d247966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246618, d247966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25517 (p : Pattern) (selected : d246622 p = 0) : d247974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246612 q = 0) : d247956 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246612, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25514 q selected
    | true =>
      simp only [d246612, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25515 q selected
  have h2 (q : Pattern) (selected : d246613 q = 0) : d247957 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246613, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246613, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246614 q = 0) : d247958 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246614, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246614, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246616 q = 0) : d247964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246616, d247964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246616, d247964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246621 q = 0) : d247973 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246621, d247973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246621, d247973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246622 q = 0) : d247974 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246622, d247974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246622, d247974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25518 (p : Pattern) (selected : d246628 p = 0) : d247980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246619 q = 0) : d247967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246619, d247967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25516 q selected
    | true =>
      simp only [d246619, d247967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246620 q = 0) : d247968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246620, d247968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246620, d247968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246623 q = 0) : d247975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246623, d247975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25517 q selected
    | true =>
      simp only [d246623, d247975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246624 q = 0) : d247976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246624, d247976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246624, d247976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246625 q = 0) : d247977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246625, d247977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246625, d247977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246626 q = 0) : d247978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246626, d247978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246626, d247978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246627 q = 0) : d247979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246627, d247979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246627, d247979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246628 q = 0) : d247980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246628, d247980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246628, d247980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25519 (p : Pattern) (selected : d246632 p = 0) : d247985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246623 q = 0) : d247975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246623, d247975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25517 q selected
    | true =>
      simp only [d246623, d247975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246624 q = 0) : d247976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246624, d247976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246624, d247976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246629 q = 0) : d247982 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246629, d247982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246629, d247982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246630 q = 0) : d247983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246630, d247983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246630, d247983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246631 q = 0) : d247984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246631, d247984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246631, d247984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246632 q = 0) : d247985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246632, d247985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246632, d247985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25520 (p : Pattern) (selected : d246640 p = 0) : d247993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246559 q = 0) : d247947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246559, d247947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25505 q selected
    | true =>
      simp only [d246559, d247947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25506 q selected
  have h2 (q : Pattern) (selected : d246560 q = 0) : d247948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246560, d247948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246560, d247948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246561 q = 0) : d247949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246561, d247949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246561, d247949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246568 q = 0) : d247956 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246568, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25506 q selected
    | true =>
      simp only [d246568, d247956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25507 q selected
  have h5 (q : Pattern) (selected : d246569 q = 0) : d247957 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246569, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246569, d247957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246570 q = 0) : d247958 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246570, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246570, d247958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246571 q = 0) : d247959 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246571, d247959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246571, d247959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246635 q = 0) : d247988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246635, d247988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25506 q selected
    | true =>
      simp only [d246635, d247988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246636 q = 0) : d247989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246636, d247989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246636, d247989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246637 q = 0) : d247990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246637, d247990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246637, d247990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246638 q = 0) : d247991 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246638, d247991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246638, d247991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d246639 q = 0) : d247992 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246639, d247992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246639, d247992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246640 q = 0) : d247993 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246640, d247993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246640, d247993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25521 (p : Pattern) (selected : d246646 p = 0) : d247999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246641 q = 0) : d247994 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246641, d247994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25520 q selected
    | true =>
      simp only [d246641, d247994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246642 q = 0) : d247995 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246642, d247995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246642, d247995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246643 q = 0) : d247996 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246643, d247996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246643, d247996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246644 q = 0) : d247997 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246644, d247997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246644, d247997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246645 q = 0) : d247998 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246645, d247998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246645, d247998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246646 q = 0) : d247999 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246646, d247999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246646, d247999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25522 (p : Pattern) (selected : d246652 p = 0) : d248005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246593 q = 0) : d247981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246593, d247981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25510 q selected
    | true =>
      simp only [d246593, d247981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25512 q selected
  have h2 (q : Pattern) (selected : d246633 q = 0) : d247986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246633, d247986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25518 q selected
    | true =>
      simp only [d246633, d247986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25519 q selected
  have h3 (q : Pattern) (selected : d246634 q = 0) : d247987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246634, d247987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246634, d247987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246647 q = 0) : d248000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246647, d248000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25521 q selected
    | true =>
      simp only [d246647, d248000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246648 q = 0) : d248001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246648, d248001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246648, d248001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246649 q = 0) : d248002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246649, d248002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246649, d248002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246650 q = 0) : d248003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246650, d248003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246650, d248003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246651 q = 0) : d248004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246651, d248004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246651, d248004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246652 q = 0) : d248005 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246652, d248005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246652, d248005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25523 (p : Pattern) (selected : d246657 p = 0) : d247985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246587 q = 0) : d247975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246587, d247975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25511 q selected
    | true =>
      simp only [d246587, d247975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246588 q = 0) : d247976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246588, d247976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246588, d247976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246654 q = 0) : d247982 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246654, d247982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246654, d247982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246655 q = 0) : d247983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246655, d247983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246655, d247983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246656 q = 0) : d247984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246656, d247984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246656, d247984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246657 q = 0) : d247985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246657, d247985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246657, d247985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25524 (p : Pattern) (selected : d246663 p = 0) : d248012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246658 q = 0) : d248007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246658, d248007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25523 q selected
    | true =>
      simp only [d246658, d248007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246659 q = 0) : d248008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246659, d248008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246659, d248008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246660 q = 0) : d248009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246660, d248009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246660, d248009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246661 q = 0) : d248010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246661, d248010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246661, d248010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246662 q = 0) : d248011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246662, d248011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246662, d248011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246663 q = 0) : d248012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246663, d248012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246663, d248012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25525 (p : Pattern) (selected : d246669 p = 0) : d248018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246383 q = 0) : d247814 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246383, d247814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246383, d247814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25466 q selected
  have h2 (q : Pattern) (selected : d246384 q = 0) : d247815 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246384, d247815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246384, d247815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246393 q = 0) : d247824 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246393, d247824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25466 q selected
    | true =>
      simp only [d246393, d247824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25469 q selected
  have h4 (q : Pattern) (selected : d246394 q = 0) : d247825 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246394, d247825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246394, d247825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246395 q = 0) : d247826 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246395, d247826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246395, d247826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246514 q = 0) : d247902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246514, d247902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25490 q selected
    | true =>
      simp only [d246514, d247902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25499 q selected
  have h7 (q : Pattern) (selected : d246527 q = 0) : d247915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246527, d247915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25500 q selected
    | true =>
      simp only [d246527, d247915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25501 q selected
  have h8 (q : Pattern) (selected : d246528 q = 0) : d247916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246528, d247916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246528, d247916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246529 q = 0) : d247917 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246529, d247917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246529, d247917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d246530 q = 0) : d247918 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246530, d247918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246530, d247918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246534 q = 0) : d247922 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246534, d247922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246534, d247922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25502 q selected
  have h12 (q : Pattern) (selected : d246536 q = 0) : d247924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246536, d247924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246536, d247924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25503 q selected
  have h13 (q : Pattern) (selected : d246537 q = 0) : d247925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246537, d247925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246537, d247925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d246538 q = 0) : d247926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246538, d247926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246538, d247926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d246539 q = 0) : d247927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246539, d247927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d246539, d247927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d246540 q = 0) : d247928 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246540, d247928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246540, d247928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d246653 q = 0) : d248006 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246653, d248006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246653, d248006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25522 q selected
  have h18 (q : Pattern) (selected : d246664 q = 0) : d248013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246664, d248013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246664, d248013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25524 q selected
  have h19 (q : Pattern) (selected : d246665 q = 0) : d248014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246665, d248014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d246665, d248014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d246666 q = 0) : d248015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246666, d248015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d246666, d248015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d246667 q = 0) : d248016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246667, d248016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d246667, d248016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d246668 q = 0) : d248017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246668, d248017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d246668, d248017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d246669 q = 0) : d248018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d246669, d248018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d246669, d248018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro25526 (p : Pattern) (selected : d246675 p = 0) : d248024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246670 q = 0) : d248019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d246670, d248019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246670, d248019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25525 q selected
  have h2 (q : Pattern) (selected : d246671 q = 0) : d248020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d246671, d248020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246671, d248020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246672 q = 0) : d248021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d246672, d248021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246672, d248021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246673 q = 0) : d248022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d246673, d248022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246673, d248022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246674 q = 0) : d248023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d246674, d248023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246674, d248023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246675 q = 0) : d248024 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d246675, d248024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246675, d248024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25527 (p : Pattern) (selected : d10053 p = 0) : d101480 p = 1 := by
  have h0 (q : Pattern) (selected : d1527 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro460 q selected
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro461 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1528 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h3 (q : Pattern) (selected : d1529 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10051 q = 0) : d101478 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10052 q = 0) : d101479 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10053 q = 0) : d101480 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro25528 (p : Pattern) (selected : d10083 p = 0) : d101510 p = 1 := by
  have h0 (q : Pattern) (selected : d1543 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro463 q selected
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro464 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1544 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h3 (q : Pattern) (selected : d1545 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10057 q = 0) : d101484 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2813 q selected
    | true =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10058 q = 0) : d101485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10080 q = 0) : d101507 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d101507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10080, d101507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1549 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d1550 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d10081 q = 0) : d101508 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, d101508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10081, d101508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d10082 q = 0) : d101509 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d101509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10082, d101509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10083 q = 0) : d101510 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d101510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10083, d101510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h11 p selected
theorem eqIntro25529 (p : Pattern) (selected : d246687 p = 0) : d248036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246679 q = 0) : d248028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246679, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25527 q selected
    | true =>
      simp only [d246679, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246680 q = 0) : d248029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246680, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246680, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246681 q = 0) : d248030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246681, d248030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246681, d248030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246682 q = 0) : d248031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246682, d248031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246682, d248031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246683 q = 0) : d248032 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246683, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25528 q selected
    | true =>
      simp only [d246683, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246684 q = 0) : d248033 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246684, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246684, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246685 q = 0) : d248034 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246685, d248034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246685, d248034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246686 q = 0) : d248035 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246686, d248035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246686, d248035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246687 q = 0) : d248036 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246687, d248036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246687, d248036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25530 (p : Pattern) (selected : d246688 p = 0) : d248037 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246683 q = 0) : d248032 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246683, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25528 q selected
    | true =>
      simp only [d246683, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246684 q = 0) : d248033 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246684, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246684, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246685 q = 0) : d248034 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246685, d248034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246685, d248034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246686 q = 0) : d248035 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246686, d248035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246686, d248035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246688 q = 0) : d248037 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246688, d248037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246688, d248037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25531 (p : Pattern) (selected : d10133 p = 0) : d101560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1575 q = 0) : d53016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
  have h2 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h3 (q : Pattern) (selected : d1576 q = 0) : d53017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1593 q = 0) : d53034 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d53034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1593, d53034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10129 q = 0) : d101556 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10130 q = 0) : d101557 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10131 q = 0) : d101558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10132 q = 0) : d101559 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, d101559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10132, d101559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10133 q = 0) : d101560 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, d101560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10133, d101560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25532 (p : Pattern) (selected : d246696 p = 0) : d248045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246692 q = 0) : d248041 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246692, d248041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25531 q selected
    | true =>
      simp only [d246692, d248041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246693 q = 0) : d248042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246693, d248042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246693, d248042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246694 q = 0) : d248043 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246694, d248043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246694, d248043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246695 q = 0) : d248044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246695, d248044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246695, d248044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246696 q = 0) : d248045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246696, d248045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246696, d248045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25533 (p : Pattern) (selected : d246703 p = 0) : d248052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246689 q = 0) : d248038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246689, d248038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25529 q selected
    | true =>
      simp only [d246689, d248038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25530 q selected
  have h2 (q : Pattern) (selected : d246690 q = 0) : d248039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246690, d248039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246690, d248039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246691 q = 0) : d248040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246691, d248040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246691, d248040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246697 q = 0) : d248046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246697, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25530 q selected
    | true =>
      simp only [d246697, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25532 q selected
  have h5 (q : Pattern) (selected : d246698 q = 0) : d248047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246698, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246698, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246699 q = 0) : d248048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246699, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246699, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246700 q = 0) : d248049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246700, d248049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246700, d248049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246701 q = 0) : d248050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246701, d248050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246701, d248050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246702 q = 0) : d248051 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246702, d248051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246702, d248051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246703 q = 0) : d248052 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246703, d248052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246703, d248052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25534 (p : Pattern) (selected : d246707 p = 0) : d248056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246697 q = 0) : d248046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246697, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25530 q selected
    | true =>
      simp only [d246697, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25532 q selected
  have h2 (q : Pattern) (selected : d246698 q = 0) : d248047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246698, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246698, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246699 q = 0) : d248048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246699, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246699, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246701 q = 0) : d248050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246701, d248050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246701, d248050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246706 q = 0) : d248055 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246706, d248055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246706, d248055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246707 q = 0) : d248056 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246707, d248056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246707, d248056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25535 (p : Pattern) (selected : d246713 p = 0) : d248062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246704 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25533 q selected
    | true =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246705 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246710 q = 0) : d248059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246711 q = 0) : d248060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246711, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246711, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246712 q = 0) : d248061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246712, d248061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246712, d248061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246713 q = 0) : d248062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246713, d248062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246713, d248062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25536 (p : Pattern) (selected : d246717 p = 0) : d248066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246714 q = 0) : d248063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246715 q = 0) : d248064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246715, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246715, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246716 q = 0) : d248065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246716, d248065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246716, d248065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246717 q = 0) : d248066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246717, d248066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246717, d248066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25537 (p : Pattern) (selected : d246723 p = 0) : d248072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246718 q = 0) : d248067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246718, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25535 q selected
    | true =>
      simp only [d246718, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25536 q selected
  have h2 (q : Pattern) (selected : d246719 q = 0) : d248068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246719, d248068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246719, d248068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246720 q = 0) : d248069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246720, d248069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246720, d248069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246721 q = 0) : d248070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246721, d248070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246721, d248070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246722 q = 0) : d248071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246722, d248071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246722, d248071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246723 q = 0) : d248072 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246723, d248072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246723, d248072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25538 (p : Pattern) (selected : d246726 p = 0) : d248075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246704 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25533 q selected
    | true =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246705 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246710 q = 0) : d248059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246711 q = 0) : d248060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246711, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246711, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246712 q = 0) : d248061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246712, d248061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246712, d248061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246726 q = 0) : d248075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246726, d248075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246726, d248075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25539 (p : Pattern) (selected : d246727 p = 0) : d248076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246714 q = 0) : d248063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246715 q = 0) : d248064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246715, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246715, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246716 q = 0) : d248065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246716, d248065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246716, d248065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246727 q = 0) : d248076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246727, d248076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246727, d248076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25540 (p : Pattern) (selected : d246733 p = 0) : d248082 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246718 q = 0) : d248067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246718, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25535 q selected
    | true =>
      simp only [d246718, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25536 q selected
  have h2 (q : Pattern) (selected : d246719 q = 0) : d248068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246719, d248068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246719, d248068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246720 q = 0) : d248069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246720, d248069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246720, d248069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246721 q = 0) : d248070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246721, d248070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246721, d248070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246722 q = 0) : d248071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246722, d248071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246722, d248071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246728 q = 0) : d248077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246728, d248077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25538 q selected
    | true =>
      simp only [d246728, d248077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25539 q selected
  have h7 (q : Pattern) (selected : d246729 q = 0) : d248078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246729, d248078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246729, d248078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246730 q = 0) : d248079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246730, d248079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246730, d248079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246731 q = 0) : d248080 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246731, d248080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246731, d248080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246732 q = 0) : d248081 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246732, d248081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246732, d248081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246733 q = 0) : d248082 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246733, d248082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246733, d248082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro25541 (p : Pattern) (selected : d246738 p = 0) : d248087 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246704 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25533 q selected
    | true =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246705 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246710 q = 0) : d248059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246711 q = 0) : d248060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246711, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246711, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246737 q = 0) : d248086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246737, d248086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246737, d248086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246738 q = 0) : d248087 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246738, d248087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246738, d248087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25542 (p : Pattern) (selected : d246740 p = 0) : d248089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246714 q = 0) : d248063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246715 q = 0) : d248064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246715, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246715, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246739 q = 0) : d248088 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246739, d248088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246739, d248088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246740 q = 0) : d248089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246740, d248089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246740, d248089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25543 (p : Pattern) (selected : d246747 p = 0) : d248096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246704 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25533 q selected
    | true =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246705 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246710 q = 0) : d248059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246745 q = 0) : d248094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246745, d248094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246745, d248094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246746 q = 0) : d248095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246746, d248095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246746, d248095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246747 q = 0) : d248096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246747, d248096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246747, d248096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25544 (p : Pattern) (selected : d246750 p = 0) : d248099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246714 q = 0) : d248063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246748 q = 0) : d248097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246748, d248097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246748, d248097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246749 q = 0) : d248098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246749, d248098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246749, d248098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246750 q = 0) : d248099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246750, d248099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246750, d248099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25545 (p : Pattern) (selected : d10044 p = 0) : d101471 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1200 q = 0) : d52781 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro405 q selected
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1201 q = 0) : d52782 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10042 q = 0) : d101469 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10043 q = 0) : d101470 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d101470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10043, d101470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10044 q = 0) : d101471 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d101471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10044, d101471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25546 (p : Pattern) (selected : d246758 p = 0) : d248107 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246754 q = 0) : d248103 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246754, d248103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25545 q selected
    | true =>
      simp only [d246754, d248103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246755 q = 0) : d248104 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246755, d248104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246755, d248104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246756 q = 0) : d248105 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246756, d248105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246756, d248105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246757 q = 0) : d248106 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246757, d248106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246757, d248106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246679 q = 0) : d248028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246679, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25527 q selected
    | true =>
      simp only [d246679, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246680 q = 0) : d248029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246680, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246680, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246681 q = 0) : d248030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246681, d248030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246681, d248030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246682 q = 0) : d248031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246682, d248031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246682, d248031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246758 q = 0) : d248107 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246758, d248107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246758, d248107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25547 (p : Pattern) (selected : d246764 p = 0) : d248113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246759 q = 0) : d248108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246759, d248108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25546 q selected
    | true =>
      simp only [d246759, d248108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25529 q selected
  have h2 (q : Pattern) (selected : d246760 q = 0) : d248109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246760, d248109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246760, d248109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246761 q = 0) : d248110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246761, d248110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246761, d248110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246689 q = 0) : d248038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246689, d248038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25529 q selected
    | true =>
      simp only [d246689, d248038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25530 q selected
  have h5 (q : Pattern) (selected : d246690 q = 0) : d248039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246690, d248039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246690, d248039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246691 q = 0) : d248040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246691, d248040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246691, d248040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246762 q = 0) : d248111 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246762, d248111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246762, d248111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246697 q = 0) : d248046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246697, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25530 q selected
    | true =>
      simp only [d246697, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25532 q selected
  have h9 (q : Pattern) (selected : d246698 q = 0) : d248047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246698, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246698, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246699 q = 0) : d248048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246699, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246699, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246700 q = 0) : d248049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246700, d248049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246700, d248049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246763 q = 0) : d248112 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246763, d248112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246763, d248112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246764 q = 0) : d248113 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246764, d248113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246764, d248113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25548 (p : Pattern) (selected : d246770 p = 0) : d248119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246765 q = 0) : d248114 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246765, d248114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25547 q selected
    | true =>
      simp only [d246765, d248114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246766 q = 0) : d248115 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246766, d248115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246766, d248115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246704 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25533 q selected
    | true =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246705 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246767 q = 0) : d248116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246767, d248116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246767, d248116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246768 q = 0) : d248117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246768, d248117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246768, d248117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246769 q = 0) : d248118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246769, d248118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246769, d248118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246770 q = 0) : d248119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246770, d248119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246770, d248119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25549 (p : Pattern) (selected : d10198 p = 0) : d101480 p = 1 := by
  have h0 (q : Pattern) (selected : d1695 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1695, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro492 q selected
    | true =>
      simp only [d1695, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro493 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1696 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1696, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1696, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro412 q selected
  have h3 (q : Pattern) (selected : d1697 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1697, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1697, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10196 q = 0) : d101478 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10196, d101478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10196, d101478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10197 q = 0) : d101479 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10197, d101479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10197, d101479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10198 q = 0) : d101480 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10198, d101480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10198, d101480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro25550 (p : Pattern) (selected : d10208 p = 0) : d101510 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro496 q selected
    | true =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro497 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1715 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h3 (q : Pattern) (selected : d1716 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10184 q = 0) : d101484 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10184, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6732 q selected
    | true =>
      simp only [d10184, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10185 q = 0) : d101485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10185, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10185, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10205 q = 0) : d101507 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10205, d101507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10205, d101507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1720 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d1721 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d10206 q = 0) : d101508 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10206, d101508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10206, d101508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d10207 q = 0) : d101509 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10207, d101509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10207, d101509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10208 q = 0) : d101510 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10208, d101510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10208, d101510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h11 p selected
theorem eqIntro25551 (p : Pattern) (selected : d246780 p = 0) : d248036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246772 q = 0) : d248028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246772, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25549 q selected
    | true =>
      simp only [d246772, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246773 q = 0) : d248029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246773, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246773, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246774 q = 0) : d248030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246774, d248030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246774, d248030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246775 q = 0) : d248031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246775, d248031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246775, d248031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246776 q = 0) : d248032 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246776, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25550 q selected
    | true =>
      simp only [d246776, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246777 q = 0) : d248033 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246777, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246777, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246778 q = 0) : d248034 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246778, d248034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246778, d248034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246779 q = 0) : d248035 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246779, d248035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246779, d248035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246780 q = 0) : d248036 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246780, d248036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246780, d248036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25552 (p : Pattern) (selected : d246781 p = 0) : d248037 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246776 q = 0) : d248032 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246776, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25550 q selected
    | true =>
      simp only [d246776, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246777 q = 0) : d248033 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246777, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246777, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246778 q = 0) : d248034 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246778, d248034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246778, d248034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246779 q = 0) : d248035 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246779, d248035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246779, d248035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246781 q = 0) : d248037 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246781, d248037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246781, d248037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25553 (p : Pattern) (selected : d10253 p = 0) : d101560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1746 q = 0) : d53016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1746, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1746, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
  have h2 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h3 (q : Pattern) (selected : d1747 q = 0) : d53017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1747, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1747, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1764 q = 0) : d53034 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1764, d53034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1764, d53034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10249 q = 0) : d101556 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10249, d101556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
    | true =>
      simp only [d10249, d101556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10250 q = 0) : d101557 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10250, d101557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10250, d101557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10251 q = 0) : d101558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10251, d101558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10251, d101558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10252 q = 0) : d101559 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10252, d101559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10252, d101559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10253 q = 0) : d101560 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10253, d101560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10253, d101560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25554 (p : Pattern) (selected : d246789 p = 0) : d248045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246785 q = 0) : d248041 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246785, d248041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25553 q selected
    | true =>
      simp only [d246785, d248041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246786 q = 0) : d248042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246786, d248042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246786, d248042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246787 q = 0) : d248043 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246787, d248043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246787, d248043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246788 q = 0) : d248044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246788, d248044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246788, d248044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246789 q = 0) : d248045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246789, d248045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246789, d248045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25555 (p : Pattern) (selected : d246796 p = 0) : d248052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246782 q = 0) : d248038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246782, d248038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25551 q selected
    | true =>
      simp only [d246782, d248038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25552 q selected
  have h2 (q : Pattern) (selected : d246783 q = 0) : d248039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246783, d248039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246783, d248039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246784 q = 0) : d248040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246784, d248040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246784, d248040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246790 q = 0) : d248046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246790, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25552 q selected
    | true =>
      simp only [d246790, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25554 q selected
  have h5 (q : Pattern) (selected : d246791 q = 0) : d248047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246791, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246791, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246792 q = 0) : d248048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246792, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246792, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246793 q = 0) : d248049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246793, d248049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246793, d248049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246794 q = 0) : d248050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246794, d248050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246794, d248050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246795 q = 0) : d248051 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246795, d248051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246795, d248051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246796 q = 0) : d248052 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246796, d248052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246796, d248052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25556 (p : Pattern) (selected : d246800 p = 0) : d248056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246790 q = 0) : d248046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246790, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25552 q selected
    | true =>
      simp only [d246790, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25554 q selected
  have h2 (q : Pattern) (selected : d246791 q = 0) : d248047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246791, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246791, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246792 q = 0) : d248048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246792, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246792, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246794 q = 0) : d248050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246794, d248050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246794, d248050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246799 q = 0) : d248055 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246799, d248055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246799, d248055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246800 q = 0) : d248056 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246800, d248056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246800, d248056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25557 (p : Pattern) (selected : d246806 p = 0) : d248062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246797 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246797, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25555 q selected
    | true =>
      simp only [d246797, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246798 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246798, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246798, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246801 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246801, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25556 q selected
    | true =>
      simp only [d246801, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246802 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246802, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246802, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246803 q = 0) : d248059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246803, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246803, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246804 q = 0) : d248060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246804, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246804, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246805 q = 0) : d248061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246805, d248061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246805, d248061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246806 q = 0) : d248062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246806, d248062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246806, d248062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25558 (p : Pattern) (selected : d246810 p = 0) : d248066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246801 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246801, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25556 q selected
    | true =>
      simp only [d246801, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246802 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246802, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246802, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246807 q = 0) : d248063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246807, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246807, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246808 q = 0) : d248064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246808, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246808, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246809 q = 0) : d248065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246809, d248065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246809, d248065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246810 q = 0) : d248066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246810, d248066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246810, d248066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25559 (p : Pattern) (selected : d246818 p = 0) : d248127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246689 q = 0) : d248038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246689, d248038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25529 q selected
    | true =>
      simp only [d246689, d248038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25530 q selected
  have h2 (q : Pattern) (selected : d246690 q = 0) : d248039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246690, d248039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246690, d248039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246691 q = 0) : d248040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246691, d248040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246691, d248040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246697 q = 0) : d248046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246697, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25530 q selected
    | true =>
      simp only [d246697, d248046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25532 q selected
  have h5 (q : Pattern) (selected : d246698 q = 0) : d248047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246698, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246698, d248047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246699 q = 0) : d248048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246699, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246699, d248048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246700 q = 0) : d248049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246700, d248049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246700, d248049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246813 q = 0) : d248122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246813, d248122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25530 q selected
    | true =>
      simp only [d246813, d248122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246814 q = 0) : d248123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246814, d248123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246814, d248123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246815 q = 0) : d248124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246815, d248124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246815, d248124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246816 q = 0) : d248125 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246816, d248125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246816, d248125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d246817 q = 0) : d248126 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246817, d248126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246817, d248126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246818 q = 0) : d248127 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246818, d248127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246818, d248127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25560 (p : Pattern) (selected : d246824 p = 0) : d248133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246819 q = 0) : d248128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246819, d248128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25559 q selected
    | true =>
      simp only [d246819, d248128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246820 q = 0) : d248129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246820, d248129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246820, d248129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246821 q = 0) : d248130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246821, d248130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246821, d248130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246822 q = 0) : d248131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246822, d248131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246822, d248131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246823 q = 0) : d248132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246823, d248132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246823, d248132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246824 q = 0) : d248133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246824, d248133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246824, d248133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25561 (p : Pattern) (selected : d246830 p = 0) : d248139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246741 q = 0) : d248090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246741, d248090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25541 q selected
    | true =>
      simp only [d246741, d248090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25542 q selected
  have h2 (q : Pattern) (selected : d246742 q = 0) : d248091 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246742, d248091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246742, d248091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246743 q = 0) : d248092 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246743, d248092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246743, d248092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246744 q = 0) : d248093 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246744, d248093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246744, d248093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246751 q = 0) : d248100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246751, d248100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25543 q selected
    | true =>
      simp only [d246751, d248100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25544 q selected
  have h6 (q : Pattern) (selected : d246752 q = 0) : d248101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246752, d248101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246752, d248101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246753 q = 0) : d248102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246753, d248102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246753, d248102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246771 q = 0) : d248120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246771, d248120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25548 q selected
    | true =>
      simp only [d246771, d248120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25535 q selected
  have h9 (q : Pattern) (selected : d246811 q = 0) : d248067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246811, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25557 q selected
    | true =>
      simp only [d246811, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25558 q selected
  have h10 (q : Pattern) (selected : d246812 q = 0) : d248121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246812, d248121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246812, d248121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246825 q = 0) : d248134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246825, d248134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25560 q selected
    | true =>
      simp only [d246825, d248134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d246826 q = 0) : d248135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246826, d248135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246826, d248135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246827 q = 0) : d248136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246827, d248136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246827, d248136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d246828 q = 0) : d248137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246828, d248137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246828, d248137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d246829 q = 0) : d248138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246829, d248138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246829, d248138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246830 q = 0) : d248139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246830, d248139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246830, d248139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro25562 (p : Pattern) (selected : d246831 p = 0) : d248140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246704 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25533 q selected
    | true =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246705 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246710 q = 0) : d248059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246711 q = 0) : d248060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246711, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246711, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246737 q = 0) : d248086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246737, d248086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246737, d248086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246831 q = 0) : d248140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246831, d248140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246831, d248140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25563 (p : Pattern) (selected : d246832 p = 0) : d248141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246714 q = 0) : d248063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246715 q = 0) : d248064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246715, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246715, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246739 q = 0) : d248088 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246739, d248088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246739, d248088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246832 q = 0) : d248141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246832, d248141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246832, d248141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25564 (p : Pattern) (selected : d246837 p = 0) : d248146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246704 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25533 q selected
    | true =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246705 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246710 q = 0) : d248059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246710, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246745 q = 0) : d248094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246745, d248094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246745, d248094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246746 q = 0) : d248095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246746, d248095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246746, d248095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246837 q = 0) : d248146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246837, d248146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246837, d248146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25565 (p : Pattern) (selected : d246838 p = 0) : d248147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246708 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25534 q selected
    | true =>
      simp only [d246708, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246709 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246709, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246714 q = 0) : d248063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246714, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246748 q = 0) : d248097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246748, d248097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246748, d248097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246749 q = 0) : d248098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246749, d248098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246749, d248098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246838 q = 0) : d248147 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246838, d248147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246838, d248147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25566 (p : Pattern) (selected : d246842 p = 0) : d248151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246765 q = 0) : d248114 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246765, d248114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25547 q selected
    | true =>
      simp only [d246765, d248114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246766 q = 0) : d248115 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246766, d248115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246766, d248115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246704 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25533 q selected
    | true =>
      simp only [d246704, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246705 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246705, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246767 q = 0) : d248116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246767, d248116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246767, d248116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246768 q = 0) : d248117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246768, d248117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246768, d248117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246769 q = 0) : d248118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246769, d248118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246769, d248118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246842 q = 0) : d248151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246842, d248151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246842, d248151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25567 (p : Pattern) (selected : d246844 p = 0) : d248075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246797 q = 0) : d248053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246797, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25555 q selected
    | true =>
      simp only [d246797, d248053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246798 q = 0) : d248054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246798, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246798, d248054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246801 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246801, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25556 q selected
    | true =>
      simp only [d246801, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246802 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246802, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246802, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246803 q = 0) : d248059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246803, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246803, d248059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246804 q = 0) : d248060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246804, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246804, d248060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246805 q = 0) : d248061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246805, d248061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246805, d248061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246844 q = 0) : d248075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246844, d248075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246844, d248075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25568 (p : Pattern) (selected : d246845 p = 0) : d248076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246801 q = 0) : d248057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246801, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25556 q selected
    | true =>
      simp only [d246801, d248057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246802 q = 0) : d248058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246802, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246802, d248058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246807 q = 0) : d248063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246807, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246807, d248063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246808 q = 0) : d248064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246808, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246808, d248064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246809 q = 0) : d248065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246809, d248065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246809, d248065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246845 q = 0) : d248076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246845, d248076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246845, d248076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25569 (p : Pattern) (selected : d246848 p = 0) : d248154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246819 q = 0) : d248128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246819, d248128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25559 q selected
    | true =>
      simp only [d246819, d248128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246820 q = 0) : d248129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246820, d248129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246820, d248129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246821 q = 0) : d248130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246821, d248130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246821, d248130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246822 q = 0) : d248131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246822, d248131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246822, d248131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246823 q = 0) : d248132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246823, d248132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246823, d248132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246848 q = 0) : d248154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246848, d248154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246848, d248154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25570 (p : Pattern) (selected : d246854 p = 0) : d248160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246741 q = 0) : d248090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246741, d248090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25541 q selected
    | true =>
      simp only [d246741, d248090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25542 q selected
  have h2 (q : Pattern) (selected : d246742 q = 0) : d248091 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246742, d248091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246742, d248091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246743 q = 0) : d248092 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246743, d248092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246743, d248092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246744 q = 0) : d248093 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246744, d248093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246744, d248093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246751 q = 0) : d248100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246751, d248100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25543 q selected
    | true =>
      simp only [d246751, d248100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25544 q selected
  have h6 (q : Pattern) (selected : d246752 q = 0) : d248101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246752, d248101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246752, d248101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246753 q = 0) : d248102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246753, d248102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246753, d248102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246771 q = 0) : d248120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246771, d248120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25548 q selected
    | true =>
      simp only [d246771, d248120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25535 q selected
  have h9 (q : Pattern) (selected : d246811 q = 0) : d248067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246811, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25557 q selected
    | true =>
      simp only [d246811, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25558 q selected
  have h10 (q : Pattern) (selected : d246812 q = 0) : d248121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246812, d248121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246812, d248121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246825 q = 0) : d248134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246825, d248134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25560 q selected
    | true =>
      simp only [d246825, d248134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d246826 q = 0) : d248135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246826, d248135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246826, d248135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246827 q = 0) : d248136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246827, d248136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246827, d248136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d246828 q = 0) : d248137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246828, d248137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246828, d248137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d246829 q = 0) : d248138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246829, d248138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246829, d248138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246833 q = 0) : d248142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246833, d248142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25562 q selected
    | true =>
      simp only [d246833, d248142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25563 q selected
  have h17 (q : Pattern) (selected : d246834 q = 0) : d248143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246834, d248143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246834, d248143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d246835 q = 0) : d248144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246835, d248144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d246835, d248144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d246836 q = 0) : d248145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246836, d248145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246836, d248145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d246839 q = 0) : d248148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246839, d248148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25564 q selected
    | true =>
      simp only [d246839, d248148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25565 q selected
  have h21 (q : Pattern) (selected : d246840 q = 0) : d248149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246840, d248149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246840, d248149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d246841 q = 0) : d248150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246841, d248150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d246841, d248150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d246843 q = 0) : d248152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246843, d248152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25566 q selected
    | true =>
      simp only [d246843, d248152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25538 q selected
  have h24 (q : Pattern) (selected : d246846 q = 0) : d248077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246846, d248077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25567 q selected
    | true =>
      simp only [d246846, d248077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25568 q selected
  have h25 (q : Pattern) (selected : d246847 q = 0) : d248153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246847, d248153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d246847, d248153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d246849 q = 0) : d248155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246849, d248155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25569 q selected
    | true =>
      simp only [d246849, d248155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d246850 q = 0) : d248156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246850, d248156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d246850, d248156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d246851 q = 0) : d248157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246851, d248157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d246851, d248157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d246852 q = 0) : d248158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246852, d248158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d246852, d248158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d246853 q = 0) : d248159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246853, d248159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d246853, d248159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d246854 q = 0) : d248160 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246854, d248160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d246854, d248160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro25571 (p : Pattern) (selected : d246861 p = 0) : d248167 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246718 q = 0) : d248067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246718, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25535 q selected
    | true =>
      simp only [d246718, d248067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25536 q selected
  have h2 (q : Pattern) (selected : d246719 q = 0) : d248068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246719, d248068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246719, d248068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246720 q = 0) : d248069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246720, d248069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246720, d248069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246721 q = 0) : d248070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246721, d248070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246721, d248070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246722 q = 0) : d248071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246722, d248071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246722, d248071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246856 q = 0) : d248162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246856, d248162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25536 q selected
    | true =>
      simp only [d246856, d248162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246857 q = 0) : d248163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246857, d248163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246857, d248163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246858 q = 0) : d248164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246858, d248164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246858, d248164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246859 q = 0) : d248165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246859, d248165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246859, d248165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246860 q = 0) : d248166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246860, d248166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246860, d248166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246861 q = 0) : d248167 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246861, d248167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246861, d248167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro25572 (p : Pattern) (selected : d246867 p = 0) : d248173 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246856 q = 0) : d248162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246856, d248162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25536 q selected
    | true =>
      simp only [d246856, d248162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246857 q = 0) : d248163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246857, d248163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246857, d248163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246858 q = 0) : d248164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246858, d248164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246858, d248164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246859 q = 0) : d248165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246859, d248165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246859, d248165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246860 q = 0) : d248166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246860, d248166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246860, d248166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246862 q = 0) : d248168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246862, d248168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25539 q selected
    | true =>
      simp only [d246862, d248168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246863 q = 0) : d248169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246863, d248169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246863, d248169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246864 q = 0) : d248170 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246864, d248170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246864, d248170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246865 q = 0) : d248171 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246865, d248171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246865, d248171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246866 q = 0) : d248172 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246866, d248172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246866, d248172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246867 q = 0) : d248173 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246867, d248173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246867, d248173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro25573 (p : Pattern) (selected : d246874 p = 0) : d248180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246843 q = 0) : d248152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246843, d248152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25566 q selected
    | true =>
      simp only [d246843, d248152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25538 q selected
  have h2 (q : Pattern) (selected : d246846 q = 0) : d248077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246846, d248077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25567 q selected
    | true =>
      simp only [d246846, d248077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25568 q selected
  have h3 (q : Pattern) (selected : d246847 q = 0) : d248153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246847, d248153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246847, d248153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246849 q = 0) : d248155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246849, d248155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25569 q selected
    | true =>
      simp only [d246849, d248155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246850 q = 0) : d248156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246850, d248156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246850, d248156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246851 q = 0) : d248157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246851, d248157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246851, d248157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246872 q = 0) : d248178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246872, d248178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246872, d248178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246873 q = 0) : d248179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246873, d248179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246873, d248179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246874 q = 0) : d248180 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246874, d248180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246874, d248180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25574 (p : Pattern) (selected : d246876 p = 0) : d248182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246862 q = 0) : d248168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246862, d248168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25539 q selected
    | true =>
      simp only [d246862, d248168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246863 q = 0) : d248169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246863, d248169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246863, d248169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246864 q = 0) : d248170 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246864, d248170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246864, d248170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246865 q = 0) : d248171 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246865, d248171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246865, d248171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246866 q = 0) : d248172 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246866, d248172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246866, d248172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246876 q = 0) : d248182 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246876, d248182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246876, d248182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25575 (p : Pattern) (selected : d246890 p = 0) : d248196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246882 q = 0) : d248188 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246882, d248188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246882, d248188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25545 q selected
  have h2 (q : Pattern) (selected : d246754 q = 0) : d248103 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246754, d248103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25545 q selected
    | true =>
      simp only [d246754, d248103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246883 q = 0) : d248189 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246883, d248189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246883, d248189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246755 q = 0) : d248104 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246755, d248104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246755, d248104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246884 q = 0) : d248190 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246884, d248190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246884, d248190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246885 q = 0) : d248191 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246885, d248191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246885, d248191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246886 q = 0) : d248192 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246886, d248192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246886, d248192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25527 q selected
  have h8 (q : Pattern) (selected : d246679 q = 0) : d248028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246679, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25527 q selected
    | true =>
      simp only [d246679, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246887 q = 0) : d248193 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246887, d248193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246887, d248193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246680 q = 0) : d248029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246680, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246680, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d246888 q = 0) : d248194 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246888, d248194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246888, d248194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246889 q = 0) : d248195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246889, d248195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246889, d248195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246890 q = 0) : d248196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246890, d248196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246890, d248196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25576 (p : Pattern) (selected : d246895 p = 0) : d248201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246886 q = 0) : d248192 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246886, d248192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246886, d248192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25527 q selected
  have h2 (q : Pattern) (selected : d246679 q = 0) : d248028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246679, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25527 q selected
    | true =>
      simp only [d246679, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246887 q = 0) : d248193 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246887, d248193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246887, d248193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246680 q = 0) : d248029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246680, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246680, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246888 q = 0) : d248194 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246888, d248194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246888, d248194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246889 q = 0) : d248195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246889, d248195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246889, d248195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246891 q = 0) : d248197 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246891, d248197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246891, d248197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25528 q selected
  have h8 (q : Pattern) (selected : d246683 q = 0) : d248032 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246683, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25528 q selected
    | true =>
      simp only [d246683, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246892 q = 0) : d248198 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246892, d248198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246892, d248198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246684 q = 0) : d248033 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246684, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246684, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d246893 q = 0) : d248199 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246893, d248199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246893, d248199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246894 q = 0) : d248200 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246894, d248200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246894, d248200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246895 q = 0) : d248201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246895, d248201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246895, d248201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25577 (p : Pattern) (selected : d246899 p = 0) : d248205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246891 q = 0) : d248197 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246891, d248197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246891, d248197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25528 q selected
  have h2 (q : Pattern) (selected : d246683 q = 0) : d248032 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246683, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25528 q selected
    | true =>
      simp only [d246683, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246892 q = 0) : d248198 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246892, d248198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246892, d248198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246684 q = 0) : d248033 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246684, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246684, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246893 q = 0) : d248199 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246893, d248199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246893, d248199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246894 q = 0) : d248200 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246894, d248200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246894, d248200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246899 q = 0) : d248205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246899, d248205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246899, d248205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25578 (p : Pattern) (selected : d246908 p = 0) : d248214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246904 q = 0) : d248210 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246904, d248210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246904, d248210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25531 q selected
  have h2 (q : Pattern) (selected : d246692 q = 0) : d248041 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246692, d248041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25531 q selected
    | true =>
      simp only [d246692, d248041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246905 q = 0) : d248211 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246905, d248211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246905, d248211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246693 q = 0) : d248042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246693, d248042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246693, d248042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246906 q = 0) : d248212 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246906, d248212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246906, d248212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246907 q = 0) : d248213 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246907, d248213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246907, d248213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246908 q = 0) : d248214 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246908, d248214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246908, d248214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25579 (p : Pattern) (selected : d246914 p = 0) : d248220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246896 q = 0) : d248202 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246896, d248202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25575 q selected
    | true =>
      simp only [d246896, d248202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25576 q selected
  have h2 (q : Pattern) (selected : d246897 q = 0) : d248203 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246897, d248203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246897, d248203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246898 q = 0) : d248204 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246898, d248204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246898, d248204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246900 q = 0) : d248206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246900, d248206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25576 q selected
    | true =>
      simp only [d246900, d248206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25577 q selected
  have h5 (q : Pattern) (selected : d246901 q = 0) : d248207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246901, d248207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246901, d248207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246902 q = 0) : d248208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246902, d248208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246902, d248208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246903 q = 0) : d248209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246903, d248209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246903, d248209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246909 q = 0) : d248215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246909, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25577 q selected
    | true =>
      simp only [d246909, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25578 q selected
  have h9 (q : Pattern) (selected : d246910 q = 0) : d248216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246910, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246910, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246911 q = 0) : d248217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246911, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246911, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246912 q = 0) : d248218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246912, d248218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246912, d248218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246913 q = 0) : d248219 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246913, d248219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246913, d248219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246914 q = 0) : d248220 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246914, d248220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246914, d248220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25580 (p : Pattern) (selected : d246919 p = 0) : d248225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246900 q = 0) : d248206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246900, d248206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25576 q selected
    | true =>
      simp only [d246900, d248206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25577 q selected
  have h2 (q : Pattern) (selected : d246901 q = 0) : d248207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246901, d248207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246901, d248207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246902 q = 0) : d248208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246902, d248208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246902, d248208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246909 q = 0) : d248215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246909, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25577 q selected
    | true =>
      simp only [d246909, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25578 q selected
  have h5 (q : Pattern) (selected : d246910 q = 0) : d248216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246910, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246910, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246911 q = 0) : d248217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246911, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246911, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246912 q = 0) : d248218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246912, d248218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246912, d248218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246917 q = 0) : d248223 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246917, d248223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246917, d248223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246918 q = 0) : d248224 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246918, d248224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246918, d248224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246919 q = 0) : d248225 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246919, d248225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246919, d248225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25581 (p : Pattern) (selected : d246925 p = 0) : d248231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246915 q = 0) : d248221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246915, d248221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25579 q selected
    | true =>
      simp only [d246915, d248221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246916 q = 0) : d248222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246916, d248222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246916, d248222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246920 q = 0) : d248226 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246920, d248226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25580 q selected
    | true =>
      simp only [d246920, d248226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246921 q = 0) : d248227 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246921, d248227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246921, d248227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246922 q = 0) : d248228 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246922, d248228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246922, d248228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246923 q = 0) : d248229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246923, d248229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246923, d248229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246924 q = 0) : d248230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246924, d248230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246924, d248230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246925 q = 0) : d248231 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246925, d248231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246925, d248231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25582 (p : Pattern) (selected : d246927 p = 0) : d248233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246909 q = 0) : d248215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246909, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25577 q selected
    | true =>
      simp only [d246909, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25578 q selected
  have h2 (q : Pattern) (selected : d246910 q = 0) : d248216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246910, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246910, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246911 q = 0) : d248217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246911, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246911, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246917 q = 0) : d248223 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246917, d248223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246917, d248223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246926 q = 0) : d248232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246926, d248232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246926, d248232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246927 q = 0) : d248233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246927, d248233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246927, d248233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25583 (p : Pattern) (selected : d246933 p = 0) : d248239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246920 q = 0) : d248226 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246920, d248226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25580 q selected
    | true =>
      simp only [d246920, d248226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246921 q = 0) : d248227 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246921, d248227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246921, d248227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246928 q = 0) : d248234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246928, d248234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25582 q selected
    | true =>
      simp only [d246928, d248234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246929 q = 0) : d248235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246929, d248235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246929, d248235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246930 q = 0) : d248236 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246930, d248236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246930, d248236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246931 q = 0) : d248237 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246931, d248237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246931, d248237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246932 q = 0) : d248238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246932, d248238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246932, d248238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246933 q = 0) : d248239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246933, d248239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246933, d248239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25584 (p : Pattern) (selected : d246943 p = 0) : d248201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246935 q = 0) : d248192 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246935, d248192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246935, d248192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25549 q selected
  have h2 (q : Pattern) (selected : d246772 q = 0) : d248028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246772, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25549 q selected
    | true =>
      simp only [d246772, d248028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246936 q = 0) : d248193 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246936, d248193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246936, d248193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246773 q = 0) : d248029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246773, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246773, d248029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246937 q = 0) : d248194 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246937, d248194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246937, d248194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246938 q = 0) : d248195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246938, d248195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246938, d248195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246939 q = 0) : d248197 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246939, d248197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246939, d248197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25550 q selected
  have h8 (q : Pattern) (selected : d246776 q = 0) : d248032 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246776, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25550 q selected
    | true =>
      simp only [d246776, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246940 q = 0) : d248198 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246940, d248198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246940, d248198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246777 q = 0) : d248033 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246777, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246777, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d246941 q = 0) : d248199 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246941, d248199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246941, d248199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246942 q = 0) : d248200 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246942, d248200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246942, d248200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246943 q = 0) : d248201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246943, d248201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246943, d248201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25585 (p : Pattern) (selected : d246944 p = 0) : d248205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246939 q = 0) : d248197 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246939, d248197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246939, d248197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25550 q selected
  have h2 (q : Pattern) (selected : d246776 q = 0) : d248032 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246776, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25550 q selected
    | true =>
      simp only [d246776, d248032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246940 q = 0) : d248198 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246940, d248198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246940, d248198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246777 q = 0) : d248033 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246777, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246777, d248033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246941 q = 0) : d248199 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246941, d248199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246941, d248199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246942 q = 0) : d248200 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246942, d248200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246942, d248200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246944 q = 0) : d248205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246944, d248205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246944, d248205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25586 (p : Pattern) (selected : d246952 p = 0) : d248214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246948 q = 0) : d248210 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246948, d248210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246948, d248210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25553 q selected
  have h2 (q : Pattern) (selected : d246785 q = 0) : d248041 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246785, d248041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25553 q selected
    | true =>
      simp only [d246785, d248041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246949 q = 0) : d248211 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246949, d248211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246949, d248211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246786 q = 0) : d248042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246786, d248042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246786, d248042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246950 q = 0) : d248212 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246950, d248212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246950, d248212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246951 q = 0) : d248213 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246951, d248213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246951, d248213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246952 q = 0) : d248214 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246952, d248214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246952, d248214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25587 (p : Pattern) (selected : d246959 p = 0) : d248225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246945 q = 0) : d248206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246945, d248206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25584 q selected
    | true =>
      simp only [d246945, d248206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25585 q selected
  have h2 (q : Pattern) (selected : d246946 q = 0) : d248207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246946, d248207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246946, d248207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246947 q = 0) : d248208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246947, d248208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246947, d248208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246953 q = 0) : d248215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246953, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25585 q selected
    | true =>
      simp only [d246953, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25586 q selected
  have h5 (q : Pattern) (selected : d246954 q = 0) : d248216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246954, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246954, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246955 q = 0) : d248217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246955, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246955, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246956 q = 0) : d248218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246956, d248218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246956, d248218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246957 q = 0) : d248223 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246957, d248223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246957, d248223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246958 q = 0) : d248224 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246958, d248224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246958, d248224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246959 q = 0) : d248225 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246959, d248225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246959, d248225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25588 (p : Pattern) (selected : d246963 p = 0) : d248233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246953 q = 0) : d248215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246953, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25585 q selected
    | true =>
      simp only [d246953, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25586 q selected
  have h2 (q : Pattern) (selected : d246954 q = 0) : d248216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246954, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246954, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246955 q = 0) : d248217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246955, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246955, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246957 q = 0) : d248223 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246957, d248223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246957, d248223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246962 q = 0) : d248232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246962, d248232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246962, d248232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246963 q = 0) : d248233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246963, d248233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246963, d248233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25589 (p : Pattern) (selected : d246969 p = 0) : d248239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246960 q = 0) : d248226 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246960, d248226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25587 q selected
    | true =>
      simp only [d246960, d248226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246961 q = 0) : d248227 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246961, d248227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246961, d248227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246964 q = 0) : d248234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246964, d248234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25588 q selected
    | true =>
      simp only [d246964, d248234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246965 q = 0) : d248235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246965, d248235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246965, d248235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246966 q = 0) : d248236 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246966, d248236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246966, d248236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246967 q = 0) : d248237 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246967, d248237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246967, d248237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246968 q = 0) : d248238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246968, d248238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246968, d248238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246969 q = 0) : d248239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246969, d248239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246969, d248239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25590 (p : Pattern) (selected : d246973 p = 0) : d248244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246964 q = 0) : d248234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246964, d248234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25588 q selected
    | true =>
      simp only [d246964, d248234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246965 q = 0) : d248235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246965, d248235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246965, d248235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246970 q = 0) : d248241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246970, d248241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246970, d248241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246971 q = 0) : d248242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246971, d248242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246971, d248242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246972 q = 0) : d248243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246972, d248243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246972, d248243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246973 q = 0) : d248244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246973, d248244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246973, d248244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25591 (p : Pattern) (selected : d246981 p = 0) : d248252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246900 q = 0) : d248206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246900, d248206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25576 q selected
    | true =>
      simp only [d246900, d248206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25577 q selected
  have h2 (q : Pattern) (selected : d246901 q = 0) : d248207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246901, d248207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246901, d248207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246902 q = 0) : d248208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246902, d248208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246902, d248208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246909 q = 0) : d248215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246909, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25577 q selected
    | true =>
      simp only [d246909, d248215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25578 q selected
  have h5 (q : Pattern) (selected : d246910 q = 0) : d248216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246910, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246910, d248216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246911 q = 0) : d248217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246911, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246911, d248217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246912 q = 0) : d248218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246912, d248218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246912, d248218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246976 q = 0) : d248247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246976, d248247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25577 q selected
    | true =>
      simp only [d246976, d248247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246977 q = 0) : d248248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246977, d248248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246977, d248248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246978 q = 0) : d248249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246978, d248249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246978, d248249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246979 q = 0) : d248250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246979, d248250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246979, d248250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d246980 q = 0) : d248251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246980, d248251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246980, d248251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246981 q = 0) : d248252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246981, d248252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246981, d248252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25592 (p : Pattern) (selected : d246987 p = 0) : d248258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246982 q = 0) : d248253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246982, d248253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25591 q selected
    | true =>
      simp only [d246982, d248253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246983 q = 0) : d248254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246983, d248254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246983, d248254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246984 q = 0) : d248255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246984, d248255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246984, d248255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246985 q = 0) : d248256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246985, d248256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246985, d248256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246986 q = 0) : d248257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246986, d248257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246986, d248257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246987 q = 0) : d248258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246987, d248258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246987, d248258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25593 (p : Pattern) (selected : d246993 p = 0) : d248264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246934 q = 0) : d248240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246934, d248240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25581 q selected
    | true =>
      simp only [d246934, d248240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25583 q selected
  have h2 (q : Pattern) (selected : d246974 q = 0) : d248245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246974, d248245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25589 q selected
    | true =>
      simp only [d246974, d248245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25590 q selected
  have h3 (q : Pattern) (selected : d246975 q = 0) : d248246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246975, d248246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246975, d248246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246988 q = 0) : d248259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246988, d248259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25592 q selected
    | true =>
      simp only [d246988, d248259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246989 q = 0) : d248260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246989, d248260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246989, d248260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246990 q = 0) : d248261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246990, d248261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246990, d248261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246991 q = 0) : d248262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246991, d248262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246991, d248262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246992 q = 0) : d248263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246992, d248263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246992, d248263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246993 q = 0) : d248264 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246993, d248264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246993, d248264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25594 (p : Pattern) (selected : d246998 p = 0) : d248244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246928 q = 0) : d248234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246928, d248234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25582 q selected
    | true =>
      simp only [d246928, d248234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246929 q = 0) : d248235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246929, d248235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246929, d248235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246995 q = 0) : d248241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246995, d248241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246995, d248241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246996 q = 0) : d248242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246996, d248242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246996, d248242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246997 q = 0) : d248243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246997, d248243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246997, d248243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246998 q = 0) : d248244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246998, d248244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246998, d248244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25595 (p : Pattern) (selected : d247004 p = 0) : d248271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246999 q = 0) : d248266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246999, d248266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25594 q selected
    | true =>
      simp only [d246999, d248266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247000 q = 0) : d248267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247000, d248267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247000, d248267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247001 q = 0) : d248268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247001, d248268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247001, d248268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247002 q = 0) : d248269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247002, d248269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247002, d248269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247003 q = 0) : d248270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247003, d248270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247003, d248270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247004 q = 0) : d248271 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247004, d248271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247004, d248271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25596 (p : Pattern) (selected : d247010 p = 0) : d248277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d246724 q = 0) : d248073 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246724, d248073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246724, d248073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25537 q selected
  have h2 (q : Pattern) (selected : d246725 q = 0) : d248074 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246725, d248074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246725, d248074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246734 q = 0) : d248083 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246734, d248083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25537 q selected
    | true =>
      simp only [d246734, d248083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25540 q selected
  have h4 (q : Pattern) (selected : d246735 q = 0) : d248084 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246735, d248084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246735, d248084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246736 q = 0) : d248085 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246736, d248085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246736, d248085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246855 q = 0) : d248161 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246855, d248161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25561 q selected
    | true =>
      simp only [d246855, d248161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25570 q selected
  have h7 (q : Pattern) (selected : d246868 q = 0) : d248174 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246868, d248174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25571 q selected
    | true =>
      simp only [d246868, d248174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25572 q selected
  have h8 (q : Pattern) (selected : d246869 q = 0) : d248175 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246869, d248175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246869, d248175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246870 q = 0) : d248176 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246870, d248176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246870, d248176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d246871 q = 0) : d248177 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246871, d248177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246871, d248177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d246875 q = 0) : d248181 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246875, d248181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246875, d248181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25573 q selected
  have h12 (q : Pattern) (selected : d246877 q = 0) : d248183 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246877, d248183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246877, d248183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25574 q selected
  have h13 (q : Pattern) (selected : d246878 q = 0) : d248184 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246878, d248184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246878, d248184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d246879 q = 0) : d248185 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246879, d248185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246879, d248185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d246880 q = 0) : d248186 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246880, d248186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d246880, d248186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d246881 q = 0) : d248187 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246881, d248187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246881, d248187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d246994 q = 0) : d248265 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246994, d248265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246994, d248265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25593 q selected
  have h18 (q : Pattern) (selected : d247005 q = 0) : d248272 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247005, d248272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247005, d248272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25595 q selected
  have h19 (q : Pattern) (selected : d247006 q = 0) : d248273 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247006, d248273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d247006, d248273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d247007 q = 0) : d248274 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247007, d248274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d247007, d248274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d247008 q = 0) : d248275 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247008, d248275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d247008, d248275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d247009 q = 0) : d248276 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247009, d248276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d247009, d248276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d247010 q = 0) : d248277 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d247010, d248277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d247010, d248277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro25597 (p : Pattern) (selected : d247016 p = 0) : d248283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247011 q = 0) : d248278 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d247011, d248278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247011, d248278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25596 q selected
  have h2 (q : Pattern) (selected : d247012 q = 0) : d248279 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d247012, d248279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247012, d248279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247013 q = 0) : d248280 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d247013, d248280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247013, d248280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247014 q = 0) : d248281 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d247014, d248281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247014, d248281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247015 q = 0) : d248282 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d247015, d248282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247015, d248282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247016 q = 0) : d248283 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d247016, d248283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247016, d248283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25598 (p : Pattern) (selected : d5717 p = 0) : d74443 p = 1 := by
  have h0 (q : Pattern) (selected : d2020 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro549 q selected
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro550 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2024 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro551 q selected
  have h3 (q : Pattern) (selected : d2025 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5715 q = 0) : d74441 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d5716 q = 0) : d74442 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d5717 q = 0) : d74443 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro25599 (p : Pattern) (selected : d10351 p = 0) : d101672 p = 1 := by
  have h0 (q : Pattern) (selected : d2004 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro546 q selected
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro547 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2008 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro548 q selected
  have h3 (q : Pattern) (selected : d2009 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10349 q = 0) : d101670 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10349, d101670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10349, d101670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10350 q = 0) : d101671 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10350, d101671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10350, d101671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10351 q = 0) : d101672 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10351, d101672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10351, d101672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro25600 (p : Pattern) (selected : d247029 p = 0) : d248296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247021 q = 0) : d248288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247021, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25599 q selected
    | true =>
      simp only [d247021, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247022 q = 0) : d248289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247022, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247022, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247023 q = 0) : d248290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247023, d248290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247023, d248290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247024 q = 0) : d248291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247024, d248291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247024, d248291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247025 q = 0) : d248292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247025, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25598 q selected
    | true =>
      simp only [d247025, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247026 q = 0) : d248293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247026, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247026, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247027 q = 0) : d248294 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247027, d248294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247027, d248294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247028 q = 0) : d248295 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247028, d248295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247028, d248295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247029 q = 0) : d248296 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247029, d248296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247029, d248296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25601 (p : Pattern) (selected : d247030 p = 0) : d248297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247025 q = 0) : d248292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247025, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25598 q selected
    | true =>
      simp only [d247025, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247026 q = 0) : d248293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247026, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247026, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247027 q = 0) : d248294 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247027, d248294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247027, d248294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247028 q = 0) : d248295 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247028, d248295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247028, d248295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247030 q = 0) : d248297 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247030, d248297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247030, d248297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25602 (p : Pattern) (selected : d10410 p = 0) : d101731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2058 q = 0) : d53337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
  have h2 (q : Pattern) (selected : d2043 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h3 (q : Pattern) (selected : d2059 q = 0) : d53338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2076 q = 0) : d53355 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10405 q = 0) : d101726 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10406 q = 0) : d101727 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10407 q = 0) : d101728 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10408 q = 0) : d101729 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10409 q = 0) : d101730 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10409, d101730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10409, d101730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10410 q = 0) : d101731 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10410, d101731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10410, d101731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25603 (p : Pattern) (selected : d247038 p = 0) : d248305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247034 q = 0) : d248301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247034, d248301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25602 q selected
    | true =>
      simp only [d247034, d248301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247035 q = 0) : d248302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247035, d248302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247035, d248302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247036 q = 0) : d248303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247036, d248303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247036, d248303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247037 q = 0) : d248304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247037, d248304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247037, d248304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247038 q = 0) : d248305 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247038, d248305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247038, d248305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25604 (p : Pattern) (selected : d247045 p = 0) : d248312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247031 q = 0) : d248298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247031, d248298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25600 q selected
    | true =>
      simp only [d247031, d248298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25601 q selected
  have h2 (q : Pattern) (selected : d247032 q = 0) : d248299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247032, d248299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247032, d248299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247033 q = 0) : d248300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247033, d248300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247033, d248300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247039 q = 0) : d248306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247039, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25601 q selected
    | true =>
      simp only [d247039, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25603 q selected
  have h5 (q : Pattern) (selected : d247040 q = 0) : d248307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247040, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247040, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247041 q = 0) : d248308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247041, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247041, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247042 q = 0) : d248309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247042, d248309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247042, d248309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247043 q = 0) : d248310 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247043, d248310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247043, d248310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247044 q = 0) : d248311 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247044, d248311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247044, d248311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247045 q = 0) : d248312 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247045, d248312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247045, d248312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25605 (p : Pattern) (selected : d247049 p = 0) : d248316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247039 q = 0) : d248306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247039, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25601 q selected
    | true =>
      simp only [d247039, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25603 q selected
  have h2 (q : Pattern) (selected : d247040 q = 0) : d248307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247040, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247040, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247041 q = 0) : d248308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247041, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247041, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247043 q = 0) : d248310 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247043, d248310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247043, d248310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247048 q = 0) : d248315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247048, d248315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247048, d248315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247049 q = 0) : d248316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247049, d248316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247049, d248316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25606 (p : Pattern) (selected : d247055 p = 0) : d248322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247046 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25604 q selected
    | true =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247047 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247052 q = 0) : d248319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247053 q = 0) : d248320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247053, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247053, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247054 q = 0) : d248321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247054, d248321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247054, d248321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247055 q = 0) : d248322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247055, d248322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247055, d248322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25607 (p : Pattern) (selected : d247059 p = 0) : d248326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247056 q = 0) : d248323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247057 q = 0) : d248324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247057, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247057, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247058 q = 0) : d248325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247058, d248325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247058, d248325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247059 q = 0) : d248326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247059, d248326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247059, d248326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25608 (p : Pattern) (selected : d247065 p = 0) : d248332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247060 q = 0) : d248327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247060, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25606 q selected
    | true =>
      simp only [d247060, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25607 q selected
  have h2 (q : Pattern) (selected : d247061 q = 0) : d248328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247061, d248328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247061, d248328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247062 q = 0) : d248329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247062, d248329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247062, d248329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247063 q = 0) : d248330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247063, d248330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247063, d248330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247064 q = 0) : d248331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247064, d248331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247064, d248331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247065 q = 0) : d248332 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247065, d248332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247065, d248332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25609 (p : Pattern) (selected : d247068 p = 0) : d248335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247046 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25604 q selected
    | true =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247047 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247052 q = 0) : d248319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247053 q = 0) : d248320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247053, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247053, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247054 q = 0) : d248321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247054, d248321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247054, d248321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247068 q = 0) : d248335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247068, d248335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247068, d248335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25610 (p : Pattern) (selected : d247069 p = 0) : d248336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247056 q = 0) : d248323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247057 q = 0) : d248324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247057, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247057, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247058 q = 0) : d248325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247058, d248325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247058, d248325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247069 q = 0) : d248336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247069, d248336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247069, d248336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25611 (p : Pattern) (selected : d247075 p = 0) : d248342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247060 q = 0) : d248327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247060, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25606 q selected
    | true =>
      simp only [d247060, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25607 q selected
  have h2 (q : Pattern) (selected : d247061 q = 0) : d248328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247061, d248328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247061, d248328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247062 q = 0) : d248329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247062, d248329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247062, d248329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247063 q = 0) : d248330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247063, d248330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247063, d248330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247064 q = 0) : d248331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247064, d248331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247064, d248331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247070 q = 0) : d248337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247070, d248337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25609 q selected
    | true =>
      simp only [d247070, d248337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25610 q selected
  have h7 (q : Pattern) (selected : d247071 q = 0) : d248338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247071, d248338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247071, d248338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247072 q = 0) : d248339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247072, d248339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247072, d248339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247073 q = 0) : d248340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247073, d248340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247073, d248340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247074 q = 0) : d248341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247074, d248341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247074, d248341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247075 q = 0) : d248342 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247075, d248342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247075, d248342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro25612 (p : Pattern) (selected : d247080 p = 0) : d248347 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247046 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25604 q selected
    | true =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247047 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247052 q = 0) : d248319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247053 q = 0) : d248320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247053, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247053, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247079 q = 0) : d248346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247079, d248346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247079, d248346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247080 q = 0) : d248347 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247080, d248347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247080, d248347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25613 (p : Pattern) (selected : d247082 p = 0) : d248349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247056 q = 0) : d248323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247057 q = 0) : d248324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247057, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247057, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247081 q = 0) : d248348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247081, d248348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247081, d248348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247082 q = 0) : d248349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247082, d248349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247082, d248349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25614 (p : Pattern) (selected : d247089 p = 0) : d248356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247046 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25604 q selected
    | true =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247047 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247052 q = 0) : d248319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247087 q = 0) : d248354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247087, d248354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247087, d248354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247088 q = 0) : d248355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247088, d248355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247088, d248355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247089 q = 0) : d248356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247089, d248356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247089, d248356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25615 (p : Pattern) (selected : d247092 p = 0) : d248359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247056 q = 0) : d248323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247090 q = 0) : d248357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247090, d248357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247090, d248357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247091 q = 0) : d248358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247091, d248358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247091, d248358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247092 q = 0) : d248359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247092, d248359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247092, d248359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25616 (p : Pattern) (selected : d247096 p = 0) : d248363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247021 q = 0) : d248288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247021, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25599 q selected
    | true =>
      simp only [d247021, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247022 q = 0) : d248289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247022, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247022, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247023 q = 0) : d248290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247023, d248290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247023, d248290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247024 q = 0) : d248291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247024, d248291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247024, d248291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247096 q = 0) : d248363 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247096, d248363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247096, d248363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro25617 (p : Pattern) (selected : d247102 p = 0) : d248369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247097 q = 0) : d248364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247097, d248364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25616 q selected
    | true =>
      simp only [d247097, d248364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25600 q selected
  have h2 (q : Pattern) (selected : d247098 q = 0) : d248365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247098, d248365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247098, d248365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247099 q = 0) : d248366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247099, d248366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247099, d248366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247031 q = 0) : d248298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247031, d248298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25600 q selected
    | true =>
      simp only [d247031, d248298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25601 q selected
  have h5 (q : Pattern) (selected : d247032 q = 0) : d248299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247032, d248299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247032, d248299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247033 q = 0) : d248300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247033, d248300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247033, d248300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247100 q = 0) : d248367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247100, d248367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247100, d248367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247039 q = 0) : d248306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247039, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25601 q selected
    | true =>
      simp only [d247039, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25603 q selected
  have h9 (q : Pattern) (selected : d247040 q = 0) : d248307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247040, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247040, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247041 q = 0) : d248308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247041, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247041, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247042 q = 0) : d248309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247042, d248309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247042, d248309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d247101 q = 0) : d248368 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247101, d248368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247101, d248368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d247102 q = 0) : d248369 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247102, d248369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d247102, d248369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25618 (p : Pattern) (selected : d247108 p = 0) : d248375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247103 q = 0) : d248370 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247103, d248370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25617 q selected
    | true =>
      simp only [d247103, d248370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247104 q = 0) : d248371 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247104, d248371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247104, d248371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247046 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25604 q selected
    | true =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247047 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247105 q = 0) : d248372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247105, d248372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247105, d248372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247106 q = 0) : d248373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247106, d248373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247106, d248373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247107 q = 0) : d248374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247107, d248374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247107, d248374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247108 q = 0) : d248375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247108, d248375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247108, d248375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25619 (p : Pattern) (selected : d10466 p = 0) : d101672 p = 1 := by
  have h0 (q : Pattern) (selected : d2170 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2170, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro580 q selected
    | true =>
      simp only [d2170, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro581 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2174 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2174, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro582 q selected
  have h3 (q : Pattern) (selected : d2175 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2175, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2175, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10464 q = 0) : d101670 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10464, d101670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10464, d101670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10465 q = 0) : d101671 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10465, d101671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10465, d101671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10466 q = 0) : d101672 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10466, d101672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10466, d101672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro25620 (p : Pattern) (selected : d10475 p = 0) : d74443 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro583 q selected
    | true =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro584 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2190 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro585 q selected
  have h3 (q : Pattern) (selected : d2191 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10473 q = 0) : d74441 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10473, d74441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10473, d74441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10474 q = 0) : d74442 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10474, d74442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10474, d74442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10475 q = 0) : d74443 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10475, d74443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10475, d74443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro25621 (p : Pattern) (selected : d247118 p = 0) : d248296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247110 q = 0) : d248288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247110, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25619 q selected
    | true =>
      simp only [d247110, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247111 q = 0) : d248289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247111, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247111, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247112 q = 0) : d248290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247112, d248290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247112, d248290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247113 q = 0) : d248291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247113, d248291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247113, d248291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247114 q = 0) : d248292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247114, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25620 q selected
    | true =>
      simp only [d247114, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247115 q = 0) : d248293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247115, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247115, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247116 q = 0) : d248294 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247116, d248294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247116, d248294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247117 q = 0) : d248295 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247117, d248295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247117, d248295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247118 q = 0) : d248296 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247118, d248296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247118, d248296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25622 (p : Pattern) (selected : d247119 p = 0) : d248297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247114 q = 0) : d248292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247114, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25620 q selected
    | true =>
      simp only [d247114, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247115 q = 0) : d248293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247115, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247115, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247116 q = 0) : d248294 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247116, d248294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247116, d248294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247117 q = 0) : d248295 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247117, d248295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247117, d248295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247119 q = 0) : d248297 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247119, d248297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247119, d248297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25623 (p : Pattern) (selected : d10519 p = 0) : d101731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2224 q = 0) : d53337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2224, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2224, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
  have h2 (q : Pattern) (selected : d2209 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h3 (q : Pattern) (selected : d2225 q = 0) : d53338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2225, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2225, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2242 q = 0) : d53355 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2242, d53355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2242, d53355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10514 q = 0) : d101726 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10514, d101726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
    | true =>
      simp only [d10514, d101726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10515 q = 0) : d101727 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10515, d101727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
    | true =>
      simp only [d10515, d101727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10516 q = 0) : d101728 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10516, d101728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10516, d101728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10517 q = 0) : d101729 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10517, d101729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10517, d101729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10518 q = 0) : d101730 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10518, d101730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10518, d101730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10519 q = 0) : d101731 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10519, d101731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10519, d101731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25624 (p : Pattern) (selected : d247127 p = 0) : d248305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247123 q = 0) : d248301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247123, d248301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25623 q selected
    | true =>
      simp only [d247123, d248301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247124 q = 0) : d248302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247124, d248302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247124, d248302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247125 q = 0) : d248303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247125, d248303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247125, d248303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247126 q = 0) : d248304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247126, d248304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247126, d248304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247127 q = 0) : d248305 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247127, d248305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247127, d248305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25625 (p : Pattern) (selected : d247134 p = 0) : d248312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247120 q = 0) : d248298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247120, d248298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25621 q selected
    | true =>
      simp only [d247120, d248298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25622 q selected
  have h2 (q : Pattern) (selected : d247121 q = 0) : d248299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247121, d248299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247121, d248299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247122 q = 0) : d248300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247122, d248300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247122, d248300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247128 q = 0) : d248306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247128, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25622 q selected
    | true =>
      simp only [d247128, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25624 q selected
  have h5 (q : Pattern) (selected : d247129 q = 0) : d248307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247129, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247129, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247130 q = 0) : d248308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247130, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247130, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247131 q = 0) : d248309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247131, d248309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247131, d248309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247132 q = 0) : d248310 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247132, d248310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247132, d248310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247133 q = 0) : d248311 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247133, d248311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247133, d248311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247134 q = 0) : d248312 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247134, d248312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247134, d248312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25626 (p : Pattern) (selected : d247138 p = 0) : d248316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247128 q = 0) : d248306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247128, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25622 q selected
    | true =>
      simp only [d247128, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25624 q selected
  have h2 (q : Pattern) (selected : d247129 q = 0) : d248307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247129, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247129, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247130 q = 0) : d248308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247130, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247130, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247132 q = 0) : d248310 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247132, d248310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247132, d248310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247137 q = 0) : d248315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247137, d248315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247137, d248315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247138 q = 0) : d248316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247138, d248316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247138, d248316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25627 (p : Pattern) (selected : d247144 p = 0) : d248322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247135 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247135, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25625 q selected
    | true =>
      simp only [d247135, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247136 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247136, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247136, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247139 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247139, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25626 q selected
    | true =>
      simp only [d247139, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247140 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247140, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247140, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247141 q = 0) : d248319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247141, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247141, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247142 q = 0) : d248320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247142, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247142, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247143 q = 0) : d248321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247143, d248321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247143, d248321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247144 q = 0) : d248322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247144, d248322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247144, d248322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25628 (p : Pattern) (selected : d247148 p = 0) : d248326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247139 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247139, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25626 q selected
    | true =>
      simp only [d247139, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247140 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247140, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247140, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247145 q = 0) : d248323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247145, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247145, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247146 q = 0) : d248324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247146, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247146, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247147 q = 0) : d248325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247147, d248325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247147, d248325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247148 q = 0) : d248326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247148, d248326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247148, d248326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25629 (p : Pattern) (selected : d247156 p = 0) : d248383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247031 q = 0) : d248298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247031, d248298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25600 q selected
    | true =>
      simp only [d247031, d248298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25601 q selected
  have h2 (q : Pattern) (selected : d247032 q = 0) : d248299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247032, d248299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247032, d248299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247033 q = 0) : d248300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247033, d248300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247033, d248300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247039 q = 0) : d248306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247039, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25601 q selected
    | true =>
      simp only [d247039, d248306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25603 q selected
  have h5 (q : Pattern) (selected : d247040 q = 0) : d248307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247040, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247040, d248307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247041 q = 0) : d248308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247041, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247041, d248308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247042 q = 0) : d248309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247042, d248309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247042, d248309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247151 q = 0) : d248378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247151, d248378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25601 q selected
    | true =>
      simp only [d247151, d248378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247152 q = 0) : d248379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247152, d248379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247152, d248379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247153 q = 0) : d248380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247153, d248380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247153, d248380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247154 q = 0) : d248381 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247154, d248381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d247154, d248381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d247155 q = 0) : d248382 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247155, d248382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247155, d248382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d247156 q = 0) : d248383 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247156, d248383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d247156, d248383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25630 (p : Pattern) (selected : d247162 p = 0) : d248389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247157 q = 0) : d248384 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247157, d248384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25629 q selected
    | true =>
      simp only [d247157, d248384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247158 q = 0) : d248385 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247158, d248385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247158, d248385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247159 q = 0) : d248386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247159, d248386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247159, d248386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247160 q = 0) : d248387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247160, d248387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247160, d248387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247161 q = 0) : d248388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247161, d248388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247161, d248388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247162 q = 0) : d248389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247162, d248389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247162, d248389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25631 (p : Pattern) (selected : d247168 p = 0) : d248395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247083 q = 0) : d248350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247083, d248350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25612 q selected
    | true =>
      simp only [d247083, d248350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25613 q selected
  have h2 (q : Pattern) (selected : d247084 q = 0) : d248351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247084, d248351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247084, d248351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247085 q = 0) : d248352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247085, d248352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247085, d248352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247086 q = 0) : d248353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247086, d248353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247086, d248353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247093 q = 0) : d248360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247093, d248360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25614 q selected
    | true =>
      simp only [d247093, d248360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25615 q selected
  have h6 (q : Pattern) (selected : d247094 q = 0) : d248361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247094, d248361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247094, d248361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247095 q = 0) : d248362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247095, d248362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247095, d248362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247109 q = 0) : d248376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247109, d248376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25618 q selected
    | true =>
      simp only [d247109, d248376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25606 q selected
  have h9 (q : Pattern) (selected : d247149 q = 0) : d248327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247149, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25627 q selected
    | true =>
      simp only [d247149, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25628 q selected
  have h10 (q : Pattern) (selected : d247150 q = 0) : d248377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247150, d248377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d247150, d248377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247163 q = 0) : d248390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247163, d248390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25630 q selected
    | true =>
      simp only [d247163, d248390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d247164 q = 0) : d248391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247164, d248391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d247164, d248391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d247165 q = 0) : d248392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247165, d248392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d247165, d248392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d247166 q = 0) : d248393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247166, d248393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247166, d248393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d247167 q = 0) : d248394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247167, d248394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247167, d248394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d247168 q = 0) : d248395 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247168, d248395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247168, d248395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro25632 (p : Pattern) (selected : d247169 p = 0) : d248396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247046 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25604 q selected
    | true =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247047 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247052 q = 0) : d248319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247053 q = 0) : d248320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247053, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247053, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247079 q = 0) : d248346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247079, d248346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247079, d248346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247169 q = 0) : d248396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247169, d248396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247169, d248396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25633 (p : Pattern) (selected : d247170 p = 0) : d248397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247056 q = 0) : d248323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247057 q = 0) : d248324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247057, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247057, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247081 q = 0) : d248348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247081, d248348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247081, d248348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247170 q = 0) : d248397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247170, d248397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247170, d248397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25634 (p : Pattern) (selected : d247175 p = 0) : d248402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247046 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25604 q selected
    | true =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247047 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247052 q = 0) : d248319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247052, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247087 q = 0) : d248354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247087, d248354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247087, d248354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247088 q = 0) : d248355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247088, d248355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247088, d248355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247175 q = 0) : d248402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247175, d248402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247175, d248402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25635 (p : Pattern) (selected : d247176 p = 0) : d248403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247050 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25605 q selected
    | true =>
      simp only [d247050, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247051 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247051, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247056 q = 0) : d248323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247056, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247090 q = 0) : d248357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247090, d248357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247090, d248357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247091 q = 0) : d248358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247091, d248358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247091, d248358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247176 q = 0) : d248403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247176, d248403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247176, d248403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25636 (p : Pattern) (selected : d247180 p = 0) : d248407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247103 q = 0) : d248370 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247103, d248370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25617 q selected
    | true =>
      simp only [d247103, d248370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247104 q = 0) : d248371 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247104, d248371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247104, d248371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247046 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25604 q selected
    | true =>
      simp only [d247046, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247047 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247047, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247105 q = 0) : d248372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247105, d248372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247105, d248372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247106 q = 0) : d248373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247106, d248373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247106, d248373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247107 q = 0) : d248374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247107, d248374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247107, d248374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247180 q = 0) : d248407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247180, d248407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247180, d248407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25637 (p : Pattern) (selected : d247182 p = 0) : d248335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247135 q = 0) : d248313 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247135, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25625 q selected
    | true =>
      simp only [d247135, d248313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247136 q = 0) : d248314 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247136, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247136, d248314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247139 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247139, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25626 q selected
    | true =>
      simp only [d247139, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247140 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247140, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247140, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247141 q = 0) : d248319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247141, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247141, d248319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247142 q = 0) : d248320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247142, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247142, d248320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247143 q = 0) : d248321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247143, d248321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247143, d248321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247182 q = 0) : d248335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247182, d248335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247182, d248335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25638 (p : Pattern) (selected : d247183 p = 0) : d248336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247139 q = 0) : d248317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247139, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25626 q selected
    | true =>
      simp only [d247139, d248317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247140 q = 0) : d248318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247140, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247140, d248318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247145 q = 0) : d248323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247145, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247145, d248323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247146 q = 0) : d248324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247146, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247146, d248324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247147 q = 0) : d248325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247147, d248325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247147, d248325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247183 q = 0) : d248336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247183, d248336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247183, d248336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25639 (p : Pattern) (selected : d247186 p = 0) : d248410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247157 q = 0) : d248384 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247157, d248384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25629 q selected
    | true =>
      simp only [d247157, d248384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247158 q = 0) : d248385 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247158, d248385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247158, d248385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247159 q = 0) : d248386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247159, d248386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247159, d248386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247160 q = 0) : d248387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247160, d248387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247160, d248387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247161 q = 0) : d248388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247161, d248388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247161, d248388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247186 q = 0) : d248410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247186, d248410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247186, d248410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25640 (p : Pattern) (selected : d247192 p = 0) : d248416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247083 q = 0) : d248350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247083, d248350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25612 q selected
    | true =>
      simp only [d247083, d248350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25613 q selected
  have h2 (q : Pattern) (selected : d247084 q = 0) : d248351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247084, d248351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247084, d248351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247085 q = 0) : d248352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247085, d248352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247085, d248352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247086 q = 0) : d248353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247086, d248353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247086, d248353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247093 q = 0) : d248360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247093, d248360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25614 q selected
    | true =>
      simp only [d247093, d248360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25615 q selected
  have h6 (q : Pattern) (selected : d247094 q = 0) : d248361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247094, d248361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247094, d248361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247095 q = 0) : d248362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247095, d248362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247095, d248362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247109 q = 0) : d248376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247109, d248376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25618 q selected
    | true =>
      simp only [d247109, d248376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25606 q selected
  have h9 (q : Pattern) (selected : d247149 q = 0) : d248327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247149, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25627 q selected
    | true =>
      simp only [d247149, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25628 q selected
  have h10 (q : Pattern) (selected : d247150 q = 0) : d248377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247150, d248377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d247150, d248377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247163 q = 0) : d248390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247163, d248390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25630 q selected
    | true =>
      simp only [d247163, d248390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d247164 q = 0) : d248391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247164, d248391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d247164, d248391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d247165 q = 0) : d248392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247165, d248392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d247165, d248392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d247166 q = 0) : d248393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247166, d248393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247166, d248393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d247167 q = 0) : d248394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247167, d248394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247167, d248394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d247171 q = 0) : d248398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247171, d248398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25632 q selected
    | true =>
      simp only [d247171, d248398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25633 q selected
  have h17 (q : Pattern) (selected : d247172 q = 0) : d248399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247172, d248399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247172, d248399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d247173 q = 0) : d248400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247173, d248400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d247173, d248400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d247174 q = 0) : d248401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247174, d248401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247174, d248401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d247177 q = 0) : d248404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247177, d248404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25634 q selected
    | true =>
      simp only [d247177, d248404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25635 q selected
  have h21 (q : Pattern) (selected : d247178 q = 0) : d248405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247178, d248405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247178, d248405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d247179 q = 0) : d248406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247179, d248406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d247179, d248406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d247181 q = 0) : d248408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247181, d248408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25636 q selected
    | true =>
      simp only [d247181, d248408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25609 q selected
  have h24 (q : Pattern) (selected : d247184 q = 0) : d248337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247184, d248337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25637 q selected
    | true =>
      simp only [d247184, d248337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25638 q selected
  have h25 (q : Pattern) (selected : d247185 q = 0) : d248409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247185, d248409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d247185, d248409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d247187 q = 0) : d248411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247187, d248411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25639 q selected
    | true =>
      simp only [d247187, d248411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d247188 q = 0) : d248412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247188, d248412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d247188, d248412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d247189 q = 0) : d248413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247189, d248413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d247189, d248413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d247190 q = 0) : d248414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247190, d248414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d247190, d248414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d247191 q = 0) : d248415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247191, d248415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d247191, d248415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d247192 q = 0) : d248416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247192, d248416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d247192, d248416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro25641 (p : Pattern) (selected : d247199 p = 0) : d248423 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247060 q = 0) : d248327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247060, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25606 q selected
    | true =>
      simp only [d247060, d248327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25607 q selected
  have h2 (q : Pattern) (selected : d247061 q = 0) : d248328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247061, d248328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247061, d248328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247062 q = 0) : d248329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247062, d248329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247062, d248329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247063 q = 0) : d248330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247063, d248330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247063, d248330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247064 q = 0) : d248331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247064, d248331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247064, d248331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247194 q = 0) : d248418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247194, d248418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25607 q selected
    | true =>
      simp only [d247194, d248418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247195 q = 0) : d248419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247195, d248419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247195, d248419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247196 q = 0) : d248420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247196, d248420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247196, d248420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247197 q = 0) : d248421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247197, d248421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247197, d248421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247198 q = 0) : d248422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247198, d248422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247198, d248422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247199 q = 0) : d248423 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247199, d248423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247199, d248423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro25642 (p : Pattern) (selected : d247205 p = 0) : d248429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247194 q = 0) : d248418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247194, d248418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25607 q selected
    | true =>
      simp only [d247194, d248418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247195 q = 0) : d248419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247195, d248419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247195, d248419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247196 q = 0) : d248420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247196, d248420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247196, d248420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247197 q = 0) : d248421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247197, d248421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247197, d248421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247198 q = 0) : d248422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247198, d248422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247198, d248422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247200 q = 0) : d248424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247200, d248424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25610 q selected
    | true =>
      simp only [d247200, d248424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247201 q = 0) : d248425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247201, d248425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247201, d248425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247202 q = 0) : d248426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247202, d248426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247202, d248426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247203 q = 0) : d248427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247203, d248427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247203, d248427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247204 q = 0) : d248428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247204, d248428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247204, d248428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247205 q = 0) : d248429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247205, d248429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247205, d248429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro25643 (p : Pattern) (selected : d247212 p = 0) : d248436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247181 q = 0) : d248408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247181, d248408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25636 q selected
    | true =>
      simp only [d247181, d248408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25609 q selected
  have h2 (q : Pattern) (selected : d247184 q = 0) : d248337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247184, d248337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25637 q selected
    | true =>
      simp only [d247184, d248337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25638 q selected
  have h3 (q : Pattern) (selected : d247185 q = 0) : d248409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247185, d248409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247185, d248409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247187 q = 0) : d248411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247187, d248411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25639 q selected
    | true =>
      simp only [d247187, d248411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247188 q = 0) : d248412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247188, d248412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247188, d248412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247189 q = 0) : d248413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247189, d248413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247189, d248413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247210 q = 0) : d248434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247210, d248434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247210, d248434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247211 q = 0) : d248435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247211, d248435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247211, d248435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d247212 q = 0) : d248436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247212, d248436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247212, d248436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25644 (p : Pattern) (selected : d247214 p = 0) : d248438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247200 q = 0) : d248424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247200, d248424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25610 q selected
    | true =>
      simp only [d247200, d248424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247201 q = 0) : d248425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247201, d248425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247201, d248425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247202 q = 0) : d248426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247202, d248426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247202, d248426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247203 q = 0) : d248427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247203, d248427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247203, d248427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247204 q = 0) : d248428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247204, d248428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247204, d248428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247214 q = 0) : d248438 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247214, d248438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247214, d248438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25645 (p : Pattern) (selected : d247224 p = 0) : d248448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247220 q = 0) : d248444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247220, d248444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247220, d248444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25599 q selected
  have h2 (q : Pattern) (selected : d247021 q = 0) : d248288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247021, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25599 q selected
    | true =>
      simp only [d247021, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247221 q = 0) : d248445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247221, d248445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247221, d248445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247022 q = 0) : d248289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247022, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247022, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247222 q = 0) : d248446 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247222, d248446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247222, d248446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247223 q = 0) : d248447 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247223, d248447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247223, d248447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247224 q = 0) : d248448 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247224, d248448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247224, d248448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro25646 (p : Pattern) (selected : d247229 p = 0) : d248453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247220 q = 0) : d248444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247220, d248444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247220, d248444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25599 q selected
  have h2 (q : Pattern) (selected : d247021 q = 0) : d248288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247021, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25599 q selected
    | true =>
      simp only [d247021, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247221 q = 0) : d248445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247221, d248445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247221, d248445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247022 q = 0) : d248289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247022, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247022, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247222 q = 0) : d248446 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247222, d248446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247222, d248446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247223 q = 0) : d248447 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247223, d248447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247223, d248447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247225 q = 0) : d248449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247225, d248449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247225, d248449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25598 q selected
  have h8 (q : Pattern) (selected : d247025 q = 0) : d248292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247025, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25598 q selected
    | true =>
      simp only [d247025, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247226 q = 0) : d248450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247226, d248450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247226, d248450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247026 q = 0) : d248293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247026, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d247026, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d247227 q = 0) : d248451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247227, d248451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247227, d248451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d247228 q = 0) : d248452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247228, d248452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d247228, d248452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d247229 q = 0) : d248453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247229, d248453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247229, d248453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25647 (p : Pattern) (selected : d247233 p = 0) : d248457 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247225 q = 0) : d248449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247225, d248449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247225, d248449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25598 q selected
  have h2 (q : Pattern) (selected : d247025 q = 0) : d248292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247025, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25598 q selected
    | true =>
      simp only [d247025, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247226 q = 0) : d248450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247226, d248450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247226, d248450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247026 q = 0) : d248293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247026, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247026, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247227 q = 0) : d248451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247227, d248451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247227, d248451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247228 q = 0) : d248452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247228, d248452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247228, d248452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247233 q = 0) : d248457 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247233, d248457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247233, d248457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25648 (p : Pattern) (selected : d247242 p = 0) : d248466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247238 q = 0) : d248462 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247238, d248462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247238, d248462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25602 q selected
  have h2 (q : Pattern) (selected : d247034 q = 0) : d248301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247034, d248301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25602 q selected
    | true =>
      simp only [d247034, d248301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247239 q = 0) : d248463 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247239, d248463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247239, d248463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247035 q = 0) : d248302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247035, d248302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247035, d248302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247240 q = 0) : d248464 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247240, d248464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247240, d248464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247241 q = 0) : d248465 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247241, d248465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247241, d248465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247242 q = 0) : d248466 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247242, d248466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247242, d248466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25649 (p : Pattern) (selected : d247248 p = 0) : d248472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247230 q = 0) : d248454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247230, d248454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25645 q selected
    | true =>
      simp only [d247230, d248454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25646 q selected
  have h2 (q : Pattern) (selected : d247231 q = 0) : d248455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247231, d248455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247231, d248455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247232 q = 0) : d248456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247232, d248456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247232, d248456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247234 q = 0) : d248458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247234, d248458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25646 q selected
    | true =>
      simp only [d247234, d248458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25647 q selected
  have h5 (q : Pattern) (selected : d247235 q = 0) : d248459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247235, d248459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247235, d248459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247236 q = 0) : d248460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247236, d248460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247236, d248460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247237 q = 0) : d248461 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247237, d248461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247237, d248461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247243 q = 0) : d248467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247243, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25647 q selected
    | true =>
      simp only [d247243, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25648 q selected
  have h9 (q : Pattern) (selected : d247244 q = 0) : d248468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247244, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247244, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247245 q = 0) : d248469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247245, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247245, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247246 q = 0) : d248470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247246, d248470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247246, d248470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d247247 q = 0) : d248471 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247247, d248471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247247, d248471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d247248 q = 0) : d248472 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247248, d248472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d247248, d248472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25650 (p : Pattern) (selected : d247253 p = 0) : d248477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247234 q = 0) : d248458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247234, d248458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25646 q selected
    | true =>
      simp only [d247234, d248458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25647 q selected
  have h2 (q : Pattern) (selected : d247235 q = 0) : d248459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247235, d248459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247235, d248459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247236 q = 0) : d248460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247236, d248460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247236, d248460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247243 q = 0) : d248467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247243, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25647 q selected
    | true =>
      simp only [d247243, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25648 q selected
  have h5 (q : Pattern) (selected : d247244 q = 0) : d248468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247244, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247244, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247245 q = 0) : d248469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247245, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247245, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247246 q = 0) : d248470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247246, d248470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247246, d248470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247251 q = 0) : d248475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247251, d248475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247251, d248475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247252 q = 0) : d248476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247252, d248476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247252, d248476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247253 q = 0) : d248477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247253, d248477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247253, d248477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25651 (p : Pattern) (selected : d247259 p = 0) : d248483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247249 q = 0) : d248473 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247249, d248473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25649 q selected
    | true =>
      simp only [d247249, d248473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247250 q = 0) : d248474 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247250, d248474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247250, d248474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247254 q = 0) : d248478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247254, d248478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25650 q selected
    | true =>
      simp only [d247254, d248478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247255 q = 0) : d248479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247255, d248479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247255, d248479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247256 q = 0) : d248480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247256, d248480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247256, d248480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247257 q = 0) : d248481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247257, d248481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247257, d248481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247258 q = 0) : d248482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247258, d248482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247258, d248482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247259 q = 0) : d248483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247259, d248483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247259, d248483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25652 (p : Pattern) (selected : d247261 p = 0) : d248485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247243 q = 0) : d248467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247243, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25647 q selected
    | true =>
      simp only [d247243, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25648 q selected
  have h2 (q : Pattern) (selected : d247244 q = 0) : d248468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247244, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247244, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247245 q = 0) : d248469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247245, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247245, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247251 q = 0) : d248475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247251, d248475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247251, d248475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247260 q = 0) : d248484 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247260, d248484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247260, d248484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247261 q = 0) : d248485 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247261, d248485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247261, d248485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25653 (p : Pattern) (selected : d247267 p = 0) : d248491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247254 q = 0) : d248478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247254, d248478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25650 q selected
    | true =>
      simp only [d247254, d248478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247255 q = 0) : d248479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247255, d248479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247255, d248479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247262 q = 0) : d248486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247262, d248486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25652 q selected
    | true =>
      simp only [d247262, d248486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247263 q = 0) : d248487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247263, d248487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247263, d248487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247264 q = 0) : d248488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247264, d248488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247264, d248488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247265 q = 0) : d248489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247265, d248489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247265, d248489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247266 q = 0) : d248490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247266, d248490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247266, d248490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247267 q = 0) : d248491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247267, d248491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247267, d248491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25654 (p : Pattern) (selected : d247277 p = 0) : d248453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247269 q = 0) : d248444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247269, d248444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247269, d248444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25619 q selected
  have h2 (q : Pattern) (selected : d247110 q = 0) : d248288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247110, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25619 q selected
    | true =>
      simp only [d247110, d248288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247270 q = 0) : d248445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247270, d248445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247270, d248445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247111 q = 0) : d248289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247111, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247111, d248289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247271 q = 0) : d248446 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247271, d248446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247271, d248446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247272 q = 0) : d248447 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247272, d248447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247272, d248447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247273 q = 0) : d248449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247273, d248449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247273, d248449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25620 q selected
  have h8 (q : Pattern) (selected : d247114 q = 0) : d248292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247114, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25620 q selected
    | true =>
      simp only [d247114, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247274 q = 0) : d248450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247274, d248450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247274, d248450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247115 q = 0) : d248293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247115, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d247115, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d247275 q = 0) : d248451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247275, d248451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247275, d248451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d247276 q = 0) : d248452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247276, d248452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d247276, d248452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d247277 q = 0) : d248453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247277, d248453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247277, d248453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25655 (p : Pattern) (selected : d247278 p = 0) : d248457 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247273 q = 0) : d248449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247273, d248449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247273, d248449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25620 q selected
  have h2 (q : Pattern) (selected : d247114 q = 0) : d248292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247114, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25620 q selected
    | true =>
      simp only [d247114, d248292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247274 q = 0) : d248450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247274, d248450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247274, d248450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247115 q = 0) : d248293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247115, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247115, d248293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247275 q = 0) : d248451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247275, d248451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247275, d248451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247276 q = 0) : d248452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247276, d248452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247276, d248452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247278 q = 0) : d248457 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247278, d248457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247278, d248457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25656 (p : Pattern) (selected : d247286 p = 0) : d248466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247282 q = 0) : d248462 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247282, d248462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247282, d248462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25623 q selected
  have h2 (q : Pattern) (selected : d247123 q = 0) : d248301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247123, d248301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25623 q selected
    | true =>
      simp only [d247123, d248301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247283 q = 0) : d248463 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247283, d248463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247283, d248463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247124 q = 0) : d248302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247124, d248302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247124, d248302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247284 q = 0) : d248464 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247284, d248464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247284, d248464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247285 q = 0) : d248465 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247285, d248465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247285, d248465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247286 q = 0) : d248466 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247286, d248466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247286, d248466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25657 (p : Pattern) (selected : d247293 p = 0) : d248477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247279 q = 0) : d248458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247279, d248458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25654 q selected
    | true =>
      simp only [d247279, d248458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25655 q selected
  have h2 (q : Pattern) (selected : d247280 q = 0) : d248459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247280, d248459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247280, d248459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247281 q = 0) : d248460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247281, d248460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247281, d248460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247287 q = 0) : d248467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247287, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25655 q selected
    | true =>
      simp only [d247287, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25656 q selected
  have h5 (q : Pattern) (selected : d247288 q = 0) : d248468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247288, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247288, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247289 q = 0) : d248469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247289, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247289, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247290 q = 0) : d248470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247290, d248470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247290, d248470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247291 q = 0) : d248475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247291, d248475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247291, d248475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247292 q = 0) : d248476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247292, d248476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247292, d248476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247293 q = 0) : d248477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247293, d248477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247293, d248477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25658 (p : Pattern) (selected : d247297 p = 0) : d248485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247287 q = 0) : d248467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247287, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25655 q selected
    | true =>
      simp only [d247287, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25656 q selected
  have h2 (q : Pattern) (selected : d247288 q = 0) : d248468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247288, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247288, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247289 q = 0) : d248469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247289, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247289, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247291 q = 0) : d248475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247291, d248475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247291, d248475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247296 q = 0) : d248484 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247296, d248484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247296, d248484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247297 q = 0) : d248485 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247297, d248485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247297, d248485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25659 (p : Pattern) (selected : d247303 p = 0) : d248491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247294 q = 0) : d248478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247294, d248478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25657 q selected
    | true =>
      simp only [d247294, d248478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247295 q = 0) : d248479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247295, d248479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247295, d248479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247298 q = 0) : d248486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247298, d248486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25658 q selected
    | true =>
      simp only [d247298, d248486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247299 q = 0) : d248487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247299, d248487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247299, d248487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247300 q = 0) : d248488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247300, d248488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247300, d248488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247301 q = 0) : d248489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247301, d248489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247301, d248489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d247302 q = 0) : d248490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247302, d248490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247302, d248490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d247303 q = 0) : d248491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247303, d248491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247303, d248491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25660 (p : Pattern) (selected : d247307 p = 0) : d248496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247298 q = 0) : d248486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247298, d248486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25658 q selected
    | true =>
      simp only [d247298, d248486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247299 q = 0) : d248487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247299, d248487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247299, d248487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247304 q = 0) : d248493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247304, d248493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247304, d248493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247305 q = 0) : d248494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247305, d248494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247305, d248494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247306 q = 0) : d248495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247306, d248495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247306, d248495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247307 q = 0) : d248496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247307, d248496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247307, d248496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25661 (p : Pattern) (selected : d247315 p = 0) : d248504 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247234 q = 0) : d248458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247234, d248458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25646 q selected
    | true =>
      simp only [d247234, d248458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25647 q selected
  have h2 (q : Pattern) (selected : d247235 q = 0) : d248459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247235, d248459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247235, d248459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247236 q = 0) : d248460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247236, d248460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247236, d248460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247243 q = 0) : d248467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247243, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25647 q selected
    | true =>
      simp only [d247243, d248467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25648 q selected
  have h5 (q : Pattern) (selected : d247244 q = 0) : d248468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247244, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247244, d248468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247245 q = 0) : d248469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247245, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247245, d248469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247246 q = 0) : d248470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247246, d248470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247246, d248470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247310 q = 0) : d248499 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247310, d248499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25647 q selected
    | true =>
      simp only [d247310, d248499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d247311 q = 0) : d248500 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247311, d248500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247311, d248500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247312 q = 0) : d248501 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247312, d248501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247312, d248501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247313 q = 0) : d248502 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247313, d248502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d247313, d248502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d247314 q = 0) : d248503 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247314, d248503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d247314, d248503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d247315 q = 0) : d248504 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247315, d248504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d247315, d248504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro25662 (p : Pattern) (selected : d247321 p = 0) : d248510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247316 q = 0) : d248505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247316, d248505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25661 q selected
    | true =>
      simp only [d247316, d248505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247317 q = 0) : d248506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247317, d248506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247317, d248506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247318 q = 0) : d248507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247318, d248507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247318, d248507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247319 q = 0) : d248508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247319, d248508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247319, d248508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247320 q = 0) : d248509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247320, d248509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247320, d248509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247321 q = 0) : d248510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247321, d248510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247321, d248510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25663 (p : Pattern) (selected : d247327 p = 0) : d248516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247268 q = 0) : d248492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247268, d248492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25651 q selected
    | true =>
      simp only [d247268, d248492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25653 q selected
  have h2 (q : Pattern) (selected : d247308 q = 0) : d248497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247308, d248497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25659 q selected
    | true =>
      simp only [d247308, d248497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25660 q selected
  have h3 (q : Pattern) (selected : d247309 q = 0) : d248498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247309, d248498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247309, d248498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247322 q = 0) : d248511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247322, d248511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25662 q selected
    | true =>
      simp only [d247322, d248511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247323 q = 0) : d248512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247323, d248512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247323, d248512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247324 q = 0) : d248513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247324, d248513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247324, d248513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247325 q = 0) : d248514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247325, d248514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247325, d248514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d247326 q = 0) : d248515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247326, d248515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247326, d248515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d247327 q = 0) : d248516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247327, d248516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247327, d248516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25664 (p : Pattern) (selected : d247332 p = 0) : d248496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247262 q = 0) : d248486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247262, d248486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25652 q selected
    | true =>
      simp only [d247262, d248486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247263 q = 0) : d248487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247263, d248487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247263, d248487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247329 q = 0) : d248493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247329, d248493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247329, d248493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247330 q = 0) : d248494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247330, d248494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247330, d248494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247331 q = 0) : d248495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247331, d248495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247331, d248495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247332 q = 0) : d248496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247332, d248496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247332, d248496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25665 (p : Pattern) (selected : d247338 p = 0) : d248523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247333 q = 0) : d248518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247333, d248518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25664 q selected
    | true =>
      simp only [d247333, d248518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247334 q = 0) : d248519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247334, d248519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247334, d248519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247335 q = 0) : d248520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247335, d248520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247335, d248520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247336 q = 0) : d248521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247336, d248521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247336, d248521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247337 q = 0) : d248522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247337, d248522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247337, d248522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247338 q = 0) : d248523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247338, d248523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247338, d248523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25666 (p : Pattern) (selected : d247344 p = 0) : d248529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247066 q = 0) : d248333 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247066, d248333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247066, d248333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25608 q selected
  have h2 (q : Pattern) (selected : d247067 q = 0) : d248334 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247067, d248334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247067, d248334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247076 q = 0) : d248343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247076, d248343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25608 q selected
    | true =>
      simp only [d247076, d248343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25611 q selected
  have h4 (q : Pattern) (selected : d247077 q = 0) : d248344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247077, d248344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247077, d248344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247078 q = 0) : d248345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247078, d248345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247078, d248345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247193 q = 0) : d248417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247193, d248417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25631 q selected
    | true =>
      simp only [d247193, d248417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25640 q selected
  have h7 (q : Pattern) (selected : d247206 q = 0) : d248430 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247206, d248430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25641 q selected
    | true =>
      simp only [d247206, d248430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25642 q selected
  have h8 (q : Pattern) (selected : d247207 q = 0) : d248431 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247207, d248431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247207, d248431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d247208 q = 0) : d248432 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247208, d248432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d247208, d248432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d247209 q = 0) : d248433 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247209, d248433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247209, d248433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247213 q = 0) : d248437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247213, d248437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247213, d248437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25643 q selected
  have h12 (q : Pattern) (selected : d247215 q = 0) : d248439 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247215, d248439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247215, d248439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25644 q selected
  have h13 (q : Pattern) (selected : d247216 q = 0) : d248440 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247216, d248440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d247216, d248440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d247217 q = 0) : d248441 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247217, d248441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d247217, d248441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d247218 q = 0) : d248442 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247218, d248442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d247218, d248442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d247219 q = 0) : d248443 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247219, d248443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d247219, d248443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d247328 q = 0) : d248517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247328, d248517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247328, d248517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25663 q selected
  have h18 (q : Pattern) (selected : d247339 q = 0) : d248524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247339, d248524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247339, d248524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25665 q selected
  have h19 (q : Pattern) (selected : d247340 q = 0) : d248525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247340, d248525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d247340, d248525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d247341 q = 0) : d248526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247341, d248526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d247341, d248526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d247342 q = 0) : d248527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247342, d248527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d247342, d248527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d247343 q = 0) : d248528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247343, d248528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d247343, d248528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d247344 q = 0) : d248529 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d247344, d248529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d247344, d248529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro25667 (p : Pattern) (selected : d247350 p = 0) : d248535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247345 q = 0) : d248530 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d247345, d248530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247345, d248530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25666 q selected
  have h2 (q : Pattern) (selected : d247346 q = 0) : d248531 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d247346, d248531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247346, d248531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d247347 q = 0) : d248532 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d247347, d248532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247347, d248532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d247348 q = 0) : d248533 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d247348, d248533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247348, d248533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d247349 q = 0) : d248534 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d247349, d248534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247349, d248534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d247350 q = 0) : d248535 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d247350, d248535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d247350, d248535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25668 (p : Pattern) (selected : d247356 p = 0) : d248541 p = 1 := by
  have h0 (q : Pattern) (selected : d246138 q = 0) : d247606 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d246138, d247606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25384 q selected
    | true =>
      simp only [d246138, d247606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25416 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d246336 q = 0) : d247767 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d246336, d247767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246336, d247767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25455 q selected
  have h3 (q : Pattern) (selected : d246337 q = 0) : d247768 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d246337, d247768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246337, d247768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246676 q = 0) : d248025 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d246676, d248025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246676, d248025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25526 q selected
  have h5 (q : Pattern) (selected : d246677 q = 0) : d248026 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d246677, d248026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246677, d248026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246678 q = 0) : d248027 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d246678, d248027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246678, d248027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d247017 q = 0) : d248284 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d247017, d248284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247017, d248284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25597 q selected
  have h8 (q : Pattern) (selected : d247018 q = 0) : d248285 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d247018, d248285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247018, d248285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d247019 q = 0) : d248286 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d247019, d248286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247019, d248286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d247020 q = 0) : d248287 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d247020, d248287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d247020, d248287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d247351 q = 0) : d248536 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d247351, d248536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247351, d248536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25667 q selected
  have h12 (q : Pattern) (selected : d247352 q = 0) : d248537 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d247352, d248537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247352, d248537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d247353 q = 0) : d248538 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d247353, d248538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247353, d248538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d247354 q = 0) : d248539 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d247354, d248539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247354, d248539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d247355 q = 0) : d248540 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d247355, d248540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d247355, d248540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d247356 q = 0) : d248541 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d247356, d248541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d247356, d248541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro25669 (p : Pattern) (selected : d247362 p = 0) : d248547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247357 q = 0) : d248542 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d247357, d248542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25668 q selected
    | true =>
      simp only [d247357, d248542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247358 q = 0) : d248543 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d247358, d248543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247358, d248543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247359 q = 0) : d248544 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d247359, d248544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247359, d248544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247360 q = 0) : d248545 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d247360, d248545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247360, d248545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247361 q = 0) : d248546 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d247361, d248546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247361, d248546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247362 q = 0) : d248547 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d247362, d248547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247362, d248547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25670 (p : Pattern) (selected : d247368 p = 0) : d248553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247363 q = 0) : d248548 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d247363, d248548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25669 q selected
    | true =>
      simp only [d247363, d248548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247364 q = 0) : d248549 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d247364, d248549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247364, d248549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247365 q = 0) : d248550 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d247365, d248550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247365, d248550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247366 q = 0) : d248551 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d247366, d248551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247366, d248551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247367 q = 0) : d248552 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d247367, d248552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247367, d248552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247368 q = 0) : d248553 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d247368, d248553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247368, d248553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25671 (p : Pattern) (selected : d247374 p = 0) : d248559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247369 q = 0) : d248554 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d247369, d248554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25670 q selected
    | true =>
      simp only [d247369, d248554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247370 q = 0) : d248555 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d247370, d248555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247370, d248555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247371 q = 0) : d248556 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d247371, d248556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247371, d248556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247372 q = 0) : d248557 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d247372, d248557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247372, d248557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247373 q = 0) : d248558 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d247373, d248558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247373, d248558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247374 q = 0) : d248559 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d247374, d248559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247374, d248559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25672 (p : Pattern) (selected : d247380 p = 0) : d248565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247375 q = 0) : d248560 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d247375, d248560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25671 q selected
    | true =>
      simp only [d247375, d248560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247376 q = 0) : d248561 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d247376, d248561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247376, d248561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247377 q = 0) : d248562 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d247377, d248562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247377, d248562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247378 q = 0) : d248563 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d247378, d248563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247378, d248563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247379 q = 0) : d248564 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d247379, d248564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247379, d248564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247380 q = 0) : d248565 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d247380, d248565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247380, d248565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25673 (p : Pattern) (selected : d247386 p = 0) : d248571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247381 q = 0) : d248566 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d247381, d248566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25672 q selected
    | true =>
      simp only [d247381, d248566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247382 q = 0) : d248567 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d247382, d248567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247382, d248567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247383 q = 0) : d248568 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d247383, d248568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247383, d248568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247384 q = 0) : d248569 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d247384, d248569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247384, d248569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247385 q = 0) : d248570 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d247385, d248570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247385, d248570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247386 q = 0) : d248571 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d247386, d248571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247386, d248571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25674 (p : Pattern) (selected : d247392 p = 0) : d248577 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247387 q = 0) : d248572 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d247387, d248572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25673 q selected
    | true =>
      simp only [d247387, d248572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247388 q = 0) : d248573 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d247388, d248573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247388, d248573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247389 q = 0) : d248574 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d247389, d248574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247389, d248574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247390 q = 0) : d248575 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d247390, d248575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247390, d248575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247391 q = 0) : d248576 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d247391, d248576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247391, d248576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247392 q = 0) : d248577 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d247392, d248577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247392, d248577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25675 (p : Pattern) (selected : d247398 p = 0) : d248583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d247393 q = 0) : d248578 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d247393, d248578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25674 q selected
    | true =>
      simp only [d247393, d248578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d247394 q = 0) : d248579 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d247394, d248579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d247394, d248579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d247395 q = 0) : d248580 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d247395, d248580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d247395, d248580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d247396 q = 0) : d248581 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d247396, d248581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247396, d248581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247397 q = 0) : d248582 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d247397, d248582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d247397, d248582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d247398 q = 0) : d248583 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d247398, d248583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d247398, d248583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25676 (p : Pattern) (selected : d245915 p = 1) : d251101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116848 q = 1) : d116848 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d116854 q = 1) : d116854 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d245910 q = 1) : d245910 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d116890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9211 q selected
    | true =>
      simp only [d116890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d245911 q = 1) : d251097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245911, d251097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d245911, d251097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116772 q = 1) : d116772 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d245912 q = 1) : d251098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245912, d251098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d245912, d251098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d245913 q = 1) : d251099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245913, d251099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d245913, d251099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d245914 q = 1) : d251100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245914, d251100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245914, d251100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d245915 q = 1) : d251101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245915, d251101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245915, d251101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro25677 (p : Pattern) (selected : d245922 p = 1) : d251106 p = 1 := by
  have h0 (q : Pattern) (selected : d116848 q = 1) : d116848 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116854 q = 1) : d116854 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d245910 q = 1) : d245910 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d116890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9211 q selected
    | true =>
      simp only [d116890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d245911 q = 1) : d251097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245911, d251097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d245911, d251097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116772 q = 1) : d116772 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d245912 q = 1) : d251098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245912, d251098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d245912, d251098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d245913 q = 1) : d251099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245913, d251099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245913, d251099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d245914 q = 1) : d251100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245914, d251100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245914, d251100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116900 q = 1) : d116900 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d116904 q = 1) : d116904 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d245917 q = 1) : d245917 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d116908 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9213 q selected
    | true =>
      simp only [d116908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d245918 q = 1) : d251102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245918, d251102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d245918, d251102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d116779 q = 1) : d116779 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d245919 q = 1) : d251103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245919, d251103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d245919, d251103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d245920 q = 1) : d251104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245920, d251104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d245920, d251104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d245921 q = 1) : d251105 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245921, d251105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d245921, d251105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d245922 q = 1) : d251106 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245922, d251106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d245922, d251106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro25678 (p : Pattern) (selected : d245929 p = 1) : d251113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245917 q = 1) : d245917 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d116908 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9213 q selected
    | true =>
      simp only [d116908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d245918 q = 1) : d251102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245918, d251102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245918, d251102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116779 q = 1) : d116779 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d245919 q = 1) : d251103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245919, d251103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d245919, d251103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d245927 q = 1) : d251111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245927, d251111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245927, d251111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d245928 q = 1) : d251112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245928, d251112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245928, d251112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d245929 q = 1) : d251113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245929, d251113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245929, d251113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25679 (p : Pattern) (selected : d245957 p = 1) : d251123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245952 q = 1) : d245952 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d116963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9218 q selected
    | true =>
      simp only [d116963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d245953 q = 1) : d251119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245953, d251119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245953, d251119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116812 q = 1) : d116812 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d245954 q = 1) : d251120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245954, d251120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d245954, d251120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d245955 q = 1) : d251121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245955, d251121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245955, d251121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d245956 q = 1) : d251122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245956, d251122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245956, d251122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d245957 q = 1) : d251123 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245957, d251123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245957, d251123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25680 (p : Pattern) (selected : d245963 p = 1) : d251129 p = 1 := by
  have h0 (q : Pattern) (selected : d116842 q = 1) : d116842 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245923 q = 1) : d251107 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245923, d251107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25676 q selected
    | true =>
      simp only [d245923, d251107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25677 q selected
  have h2 (q : Pattern) (selected : d116916 q = 1) : d116916 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d245924 q = 1) : d251108 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245924, d251108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245924, d251108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d245925 q = 1) : d251109 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245925, d251109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d245925, d251109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d245926 q = 1) : d251110 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245926, d251110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245926, d251110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d245930 q = 1) : d251114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245930, d251114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d245930, d251114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25678 q selected
  have h8 (q : Pattern) (selected : d245931 q = 1) : d251115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245931, d251115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d245931, d251115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d245932 q = 1) : d251116 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245932, d251116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d245932, d251116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d245933 q = 1) : d251117 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245933, d251117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d245933, d251117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d245934 q = 1) : d251118 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245934, d251118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d245934, d251118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d245958 q = 1) : d251124 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245958, d251124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d245958, d251124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25679 q selected
  have h13 (q : Pattern) (selected : d245959 q = 1) : d251125 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245959, d251125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d245959, d251125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d245960 q = 1) : d251126 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245960, d251126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d245960, d251126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d245961 q = 1) : d251127 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245961, d251127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d245961, d251127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d245962 q = 1) : d251128 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245962, d251128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d245962, d251128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d245963 q = 1) : d251129 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245963, d251129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d245963, d251129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro25681 (p : Pattern) (selected : d245969 p = 1) : d251135 p = 1 := by
  have h0 (q : Pattern) (selected : d116827 q = 1) : d116827 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d245964 q = 1) : d251130 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245964, d251130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245964, d251130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25680 q selected
  have h3 (q : Pattern) (selected : d245965 q = 1) : d251131 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245965, d251131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245965, d251131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d245966 q = 1) : d251132 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245966, d251132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245966, d251132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d245967 q = 1) : d251133 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245967, d251133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245967, d251133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d245968 q = 1) : d251134 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245968, d251134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d245968, d251134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d245969 q = 1) : d251135 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245969, d251135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245969, d251135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro25682 (p : Pattern) (selected : d9510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9509 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9510 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25683 (p : Pattern) (selected : d246019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25682 q selected
    | true =>
      simp only [d246015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246016 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246017 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246018 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
    | true =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246019 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25684 (p : Pattern) (selected : d246025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246020 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25683 q selected
    | true =>
      simp only [d246020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9209 q selected
  have h2 (q : Pattern) (selected : d246021 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246022 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9209 q selected
    | true =>
      simp only [d116878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246023 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116881 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246024 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246025 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25685 (p : Pattern) (selected : d246031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246026 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25684 q selected
    | true =>
      simp only [d246026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246027 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9210 q selected
    | true =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246028 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246029 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246030 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246031 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25686 (p : Pattern) (selected : d246043 p = 1) : d251140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245990 q = 1) : d245990 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d245996 q = 1) : d245996 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246014 q = 1) : d246014 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d246032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25685 q selected
    | true =>
      simp only [d246032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9211 q selected
  have h5 (q : Pattern) (selected : d246033 q = 1) : d251136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246033, d251136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246033, d251136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246039 q = 1) : d246039 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d246040 q = 1) : d251137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246040, d251137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246040, d251137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246041 q = 1) : d251138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246041, d251138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246041, d251138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246042 q = 1) : d251139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246042, d251139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246042, d251139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246043 q = 1) : d251140 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246043, d251140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246043, d251140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro25687 (p : Pattern) (selected : d246055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246026 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25684 q selected
    | true =>
      simp only [d246026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246027 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9210 q selected
    | true =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246028 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246029 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246030 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246055 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25688 (p : Pattern) (selected : d246064 p = 1) : d251145 p = 1 := by
  have h0 (q : Pattern) (selected : d245990 q = 1) : d245990 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245996 q = 1) : d245996 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246014 q = 1) : d246014 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25685 q selected
    | true =>
      simp only [d246032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9211 q selected
  have h4 (q : Pattern) (selected : d246033 q = 1) : d251136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246033, d251136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246033, d251136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246039 q = 1) : d246039 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d246040 q = 1) : d251137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246040, d251137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246040, d251137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246041 q = 1) : d251138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246041, d251138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246041, d251138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246042 q = 1) : d251139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246042, d251139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246042, d251139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246048 q = 1) : d246048 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d246052 q = 1) : d246052 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d246054 q = 1) : d246054 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d246056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25687 q selected
    | true =>
      simp only [d246056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9213 q selected
  have h13 (q : Pattern) (selected : d246057 q = 1) : d251141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246057, d251141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246057, d251141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d246060 q = 1) : d246060 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d246061 q = 1) : d251142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246061, d251142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246061, d251142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246062 q = 1) : d251143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246062, d251143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246062, d251143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d246063 q = 1) : d251144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246063, d251144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246063, d251144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d246064 q = 1) : d251145 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246064, d251145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246064, d251145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro25689 (p : Pattern) (selected : d246073 p = 1) : d251152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246054 q = 1) : d246054 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25687 q selected
    | true =>
      simp only [d246056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9213 q selected
  have h3 (q : Pattern) (selected : d246057 q = 1) : d251141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246057, d251141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246057, d251141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246060 q = 1) : d246060 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246061 q = 1) : d251142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246061, d251142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246061, d251142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246071 q = 1) : d251150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246071, d251150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246071, d251150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246072 q = 1) : d251151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246072, d251151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246072, d251151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246073 q = 1) : d251152 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246073, d251152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246073, d251152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25690 (p : Pattern) (selected : d246101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25682 q selected
  have h2 (q : Pattern) (selected : d246015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25682 q selected
    | true =>
      simp only [d246015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246016 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
  have h8 (q : Pattern) (selected : d116873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
    | true =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d116948 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d116949 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246101 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25691 (p : Pattern) (selected : d246107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246102 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25690 q selected
    | true =>
      simp only [d246102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9216 q selected
  have h2 (q : Pattern) (selected : d246103 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246104 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116951 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9216 q selected
    | true =>
      simp only [d116951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116952 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116953 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246105 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116954 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246106 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246107 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25692 (p : Pattern) (selected : d246113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25691 q selected
    | true =>
      simp only [d246108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116957 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9217 q selected
    | true =>
      simp only [d116957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116958 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246110 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246113 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25693 (p : Pattern) (selected : d246125 p = 1) : d251162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246096 q = 1) : d246096 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25692 q selected
    | true =>
      simp only [d246114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9218 q selected
  have h3 (q : Pattern) (selected : d246115 q = 1) : d251158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246115, d251158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246115, d251158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246121 q = 1) : d246121 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246122 q = 1) : d251159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246122, d251159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246122, d251159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246123 q = 1) : d251160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246123, d251160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246123, d251160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246124 q = 1) : d251161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246124, d251161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246124, d251161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246125 q = 1) : d251162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246125, d251162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246125, d251162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25694 (p : Pattern) (selected : d246131 p = 1) : d251168 p = 1 := by
  have h0 (q : Pattern) (selected : d245984 q = 1) : d245984 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246065 q = 1) : d251146 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246065, d251146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25686 q selected
    | true =>
      simp only [d246065, d251146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25688 q selected
  have h2 (q : Pattern) (selected : d246067 q = 1) : d246067 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246068 q = 1) : d251147 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246068, d251147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246068, d251147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246069 q = 1) : d251148 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246069, d251148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246069, d251148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246070 q = 1) : d251149 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246070, d251149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246070, d251149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246074 q = 1) : d251153 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246074, d251153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246074, d251153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25689 q selected
  have h8 (q : Pattern) (selected : d117087 q = 1) : d117087 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d246075 q = 1) : d251154 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246075, d251154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246075, d251154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246076 q = 1) : d251155 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246076, d251155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246076, d251155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d246077 q = 1) : d251156 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246077, d251156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246077, d251156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d246078 q = 1) : d251157 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246078, d251157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246078, d251157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246126 q = 1) : d251163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246126, d251163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246126, d251163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25693 q selected
  have h14 (q : Pattern) (selected : d117145 q = 1) : d117145 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d246127 q = 1) : d251164 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246127, d251164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246127, d251164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246128 q = 1) : d251165 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246128, d251165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d246128, d251165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d246129 q = 1) : d251166 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246129, d251166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d246129, d251166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d246130 q = 1) : d251167 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246130, d251167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d246130, d251167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d246131 q = 1) : d251168 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d246131, d251168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246131, d251168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro25695 (p : Pattern) (selected : d246137 p = 1) : d251174 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246132 q = 1) : d251169 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d246132, d251169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246132, d251169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25694 q selected
  have h2 (q : Pattern) (selected : d246133 q = 1) : d251170 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d246133, d251170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246133, d251170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246134 q = 1) : d251171 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d246134, d251171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246134, d251171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246135 q = 1) : d251172 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d246135, d251172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246135, d251172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246136 q = 1) : d251173 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d246136, d251173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246136, d251173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246137 q = 1) : d251174 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d246137, d251174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246137, d251174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25696 (p : Pattern) (selected : d9669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d568 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9655 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6822 q selected
    | true =>
      simp only [d9655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9656 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9667 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9668 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9669 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25697 (p : Pattern) (selected : d246204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246200 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25696 q selected
    | true =>
      simp only [d246200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246201 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246202 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246203 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246204 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25698 (p : Pattern) (selected : d246210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25697 q selected
    | true =>
      simp only [d246205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9238 q selected
  have h2 (q : Pattern) (selected : d246206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9238 q selected
    | true =>
      simp only [d117254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117258 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246209 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246210 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25699 (p : Pattern) (selected : d246216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246211 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25698 q selected
    | true =>
      simp only [d246211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246212 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117265 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9240 q selected
    | true =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117266 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246213 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246214 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246215 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246216 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25700 (p : Pattern) (selected : d246228 p = 1) : d251180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246175 q = 1) : d246175 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246181 q = 1) : d246181 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246199 q = 1) : d246199 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d246217 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25699 q selected
    | true =>
      simp only [d246217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9242 q selected
  have h5 (q : Pattern) (selected : d246218 q = 1) : d251176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246218, d251176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246218, d251176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246224 q = 1) : d246224 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d246225 q = 1) : d251177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246225, d251177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246225, d251177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246226 q = 1) : d251178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246226, d251178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246226, d251178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246227 q = 1) : d251179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246227, d251179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246227, d251179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246228 q = 1) : d251180 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246228, d251180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246228, d251180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro25701 (p : Pattern) (selected : d246240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246211 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25698 q selected
    | true =>
      simp only [d246211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246212 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117265 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9240 q selected
    | true =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117266 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246213 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246214 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246215 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246240 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25702 (p : Pattern) (selected : d246249 p = 1) : d251185 p = 1 := by
  have h0 (q : Pattern) (selected : d246175 q = 1) : d246175 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246181 q = 1) : d246181 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246199 q = 1) : d246199 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246217 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25699 q selected
    | true =>
      simp only [d246217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9242 q selected
  have h4 (q : Pattern) (selected : d246218 q = 1) : d251176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246218, d251176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246218, d251176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246224 q = 1) : d246224 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d246225 q = 1) : d251177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246225, d251177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246225, d251177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246226 q = 1) : d251178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246226, d251178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246226, d251178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246227 q = 1) : d251179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246227, d251179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246227, d251179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246233 q = 1) : d246233 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d246237 q = 1) : d246237 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d246239 q = 1) : d246239 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d246241 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25701 q selected
    | true =>
      simp only [d246241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9245 q selected
  have h13 (q : Pattern) (selected : d246242 q = 1) : d251181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246242, d251181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246242, d251181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d246245 q = 1) : d246245 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d246246 q = 1) : d251182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246246, d251182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246246, d251182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246247 q = 1) : d251183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246247, d251183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246247, d251183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d246248 q = 1) : d251184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246248, d251184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246248, d251184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d246249 q = 1) : d251185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246249, d251185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246249, d251185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro25703 (p : Pattern) (selected : d246258 p = 1) : d251192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246239 q = 1) : d246239 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246241 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25701 q selected
    | true =>
      simp only [d246241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9245 q selected
  have h3 (q : Pattern) (selected : d246242 q = 1) : d251181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246242, d251181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246242, d251181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246245 q = 1) : d246245 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246246 q = 1) : d251182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246246, d251182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246246, d251182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246256 q = 1) : d251190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246256, d251190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246256, d251190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246257 q = 1) : d251191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246257, d251191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246257, d251191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246258 q = 1) : d251192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246258, d251192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246258, d251192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25704 (p : Pattern) (selected : d246299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246295 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25696 q selected
  have h2 (q : Pattern) (selected : d246200 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25696 q selected
    | true =>
      simp only [d246200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246296 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246201 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246297 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246298 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117110 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
  have h8 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117111 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117112 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117113 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246299 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25705 (p : Pattern) (selected : d246305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25704 q selected
    | true =>
      simp only [d246300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9249 q selected
  have h2 (q : Pattern) (selected : d246301 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246302 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117394 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9249 q selected
    | true =>
      simp only [d117394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117395 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117396 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246303 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117398 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246304 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246305 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25706 (p : Pattern) (selected : d246311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246306 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25705 q selected
    | true =>
      simp only [d246306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9251 q selected
    | true =>
      simp only [d117405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25707 (p : Pattern) (selected : d246323 p = 1) : d251202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246294 q = 1) : d246294 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25706 q selected
    | true =>
      simp only [d246312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9253 q selected
  have h3 (q : Pattern) (selected : d246313 q = 1) : d251198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246313, d251198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246313, d251198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246319 q = 1) : d246319 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246320 q = 1) : d251199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246320, d251199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246320, d251199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246321 q = 1) : d251200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246321, d251200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246321, d251200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246322 q = 1) : d251201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246322, d251201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246322, d251201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246323 q = 1) : d251202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246323, d251202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246323, d251202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25708 (p : Pattern) (selected : d246329 p = 1) : d251208 p = 1 := by
  have h0 (q : Pattern) (selected : d246169 q = 1) : d246169 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246250 q = 1) : d251186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246250, d251186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25700 q selected
    | true =>
      simp only [d246250, d251186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25702 q selected
  have h2 (q : Pattern) (selected : d246252 q = 1) : d246252 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246253 q = 1) : d251187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246253, d251187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246253, d251187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246254 q = 1) : d251188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246254, d251188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246254, d251188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246255 q = 1) : d251189 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246255, d251189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246255, d251189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246259 q = 1) : d251193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246259, d251193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246259, d251193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25703 q selected
  have h8 (q : Pattern) (selected : d117333 q = 1) : d117333 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d246260 q = 1) : d251194 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246260, d251194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246260, d251194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246261 q = 1) : d251195 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246261, d251195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246261, d251195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d246262 q = 1) : d251196 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246262, d251196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246262, d251196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d246263 q = 1) : d251197 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246263, d251197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246263, d251197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246324 q = 1) : d251203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246324, d251203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246324, d251203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25707 q selected
  have h14 (q : Pattern) (selected : d117438 q = 1) : d117438 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d246325 q = 1) : d251204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246325, d251204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246325, d251204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246326 q = 1) : d251205 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246326, d251205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d246326, d251205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d246327 q = 1) : d251206 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246327, d251206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d246327, d251206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d246328 q = 1) : d251207 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246328, d251207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d246328, d251207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d246329 q = 1) : d251208 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d246329, d251208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246329, d251208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro25709 (p : Pattern) (selected : d246335 p = 1) : d251214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246330 q = 1) : d251209 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d246330, d251209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246330, d251209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25708 q selected
  have h2 (q : Pattern) (selected : d246331 q = 1) : d251210 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d246331, d251210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246331, d251210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246332 q = 1) : d251211 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d246332, d251211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246332, d251211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246333 q = 1) : d251212 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d246333, d251212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246333, d251212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246334 q = 1) : d251213 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d246334, d251213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246334, d251213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246335 q = 1) : d251214 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d246335, d251214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246335, d251214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25710 (p : Pattern) (selected : d9906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro49 q selected
    | true =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1238 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9902 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6835 q selected
    | true =>
      simp only [d9902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d9903 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d9904 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9905 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d9906 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro25711 (p : Pattern) (selected : d9916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9655 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6822 q selected
    | true =>
      simp only [d9655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d9656 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d9913 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d9914 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d9915 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9916 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h10 p selected
theorem eqIntro25712 (p : Pattern) (selected : d246439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25710 q selected
    | true =>
      simp only [d246431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246434 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246435 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25711 q selected
    | true =>
      simp only [d246435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246436 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246437 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246438 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246439 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25713 (p : Pattern) (selected : d246440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246435 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25711 q selected
    | true =>
      simp only [d246435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246436 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246437 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246438 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25714 (p : Pattern) (selected : d9950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h2 (q : Pattern) (selected : d1271 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1287 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9949 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9950 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25715 (p : Pattern) (selected : d246448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246444 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25714 q selected
    | true =>
      simp only [d246444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246445 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246446 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246447 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246448 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25716 (p : Pattern) (selected : d246455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246441 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25712 q selected
    | true =>
      simp only [d246441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25713 q selected
  have h2 (q : Pattern) (selected : d246442 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246443 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246449 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25713 q selected
    | true =>
      simp only [d246449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25715 q selected
  have h5 (q : Pattern) (selected : d246450 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246451 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246452 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246453 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246454 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246455 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25717 (p : Pattern) (selected : d246459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246449 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25713 q selected
    | true =>
      simp only [d246449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25715 q selected
  have h2 (q : Pattern) (selected : d246450 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246451 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246453 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246458 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246459 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25718 (p : Pattern) (selected : d246465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246456 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25716 q selected
    | true =>
      simp only [d246456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246457 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25717 q selected
    | true =>
      simp only [d246460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246462 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246463 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246464 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246465 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25719 (p : Pattern) (selected : d246469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25717 q selected
    | true =>
      simp only [d246460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246466 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246467 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246468 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246469 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25720 (p : Pattern) (selected : d246489 p = 1) : d251221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246403 q = 1) : d246403 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246412 q = 1) : d246412 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246430 q = 1) : d246430 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d246470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25718 q selected
    | true =>
      simp only [d246470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25719 q selected
  have h5 (q : Pattern) (selected : d246471 q = 1) : d251217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246471, d251217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246471, d251217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246485 q = 1) : d246485 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d246486 q = 1) : d251218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246486, d251218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246486, d251218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246487 q = 1) : d251219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246487, d251219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246487, d251219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246488 q = 1) : d251220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246488, d251220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246488, d251220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246489 q = 1) : d251221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246489, d251221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246489, d251221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro25721 (p : Pattern) (selected : d246503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246456 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25716 q selected
    | true =>
      simp only [d246456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246457 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25717 q selected
    | true =>
      simp only [d246460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246462 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246463 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246464 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246503 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25722 (p : Pattern) (selected : d246504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25717 q selected
    | true =>
      simp only [d246460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246466 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246467 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246468 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25723 (p : Pattern) (selected : d246513 p = 1) : d251226 p = 1 := by
  have h0 (q : Pattern) (selected : d246403 q = 1) : d246403 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246412 q = 1) : d246412 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246430 q = 1) : d246430 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25718 q selected
    | true =>
      simp only [d246470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25719 q selected
  have h4 (q : Pattern) (selected : d246471 q = 1) : d251217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246471, d251217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246471, d251217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246485 q = 1) : d246485 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d246486 q = 1) : d251218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246486, d251218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246486, d251218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246487 q = 1) : d251219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246487, d251219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246487, d251219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246488 q = 1) : d251220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246488, d251220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246488, d251220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246495 q = 1) : d246495 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d246500 q = 1) : d246500 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d246502 q = 1) : d246502 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d246505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25721 q selected
    | true =>
      simp only [d246505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25722 q selected
  have h13 (q : Pattern) (selected : d246506 q = 1) : d251222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246506, d251222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246506, d251222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d246509 q = 1) : d246509 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d246510 q = 1) : d251223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246510, d251223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246510, d251223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246511 q = 1) : d251224 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246511, d251224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246511, d251224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d246512 q = 1) : d251225 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246512, d251225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246512, d251225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d246513 q = 1) : d251226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246513, d251226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246513, d251226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro25724 (p : Pattern) (selected : d246533 p = 1) : d251233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246502 q = 1) : d246502 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25721 q selected
    | true =>
      simp only [d246505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25722 q selected
  have h3 (q : Pattern) (selected : d246506 q = 1) : d251222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246506, d251222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246506, d251222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246509 q = 1) : d246509 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246510 q = 1) : d251223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246510, d251223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246510, d251223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246531 q = 1) : d251231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246531, d251231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246531, d251231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246532 q = 1) : d251232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246532, d251232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246532, d251232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246533 q = 1) : d251233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246533, d251233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246533, d251233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25725 (p : Pattern) (selected : d246602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246594 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25710 q selected
  have h2 (q : Pattern) (selected : d246431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25710 q selected
    | true =>
      simp only [d246431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246595 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246596 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246597 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246598 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25711 q selected
  have h8 (q : Pattern) (selected : d246435 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25711 q selected
    | true =>
      simp only [d246435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246599 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246436 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d246600 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d246601 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d246602 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro25726 (p : Pattern) (selected : d246603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246598 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25711 q selected
  have h2 (q : Pattern) (selected : d246435 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25711 q selected
    | true =>
      simp only [d246435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246599 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246436 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246600 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246601 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25727 (p : Pattern) (selected : d246611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246607 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25714 q selected
  have h2 (q : Pattern) (selected : d246444 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25714 q selected
    | true =>
      simp only [d246444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246608 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246445 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246609 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246610 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246611 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro25728 (p : Pattern) (selected : d246618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246604 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25725 q selected
    | true =>
      simp only [d246604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25726 q selected
  have h2 (q : Pattern) (selected : d246605 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246606 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246612 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25726 q selected
    | true =>
      simp only [d246612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25727 q selected
  have h5 (q : Pattern) (selected : d246613 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246614 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246615 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246616 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246617 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246618 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25729 (p : Pattern) (selected : d246622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246612 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25726 q selected
    | true =>
      simp only [d246612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25727 q selected
  have h2 (q : Pattern) (selected : d246613 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246614 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246616 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246621 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246622 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25730 (p : Pattern) (selected : d246628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246619 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25728 q selected
    | true =>
      simp only [d246619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246620 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25729 q selected
    | true =>
      simp only [d246623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25731 (p : Pattern) (selected : d246632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25729 q selected
    | true =>
      simp only [d246623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246629 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246630 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246631 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246632 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25732 (p : Pattern) (selected : d246652 p = 1) : d251243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246593 q = 1) : d246593 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25730 q selected
    | true =>
      simp only [d246633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25731 q selected
  have h3 (q : Pattern) (selected : d246634 q = 1) : d251239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246634, d251239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246634, d251239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246648 q = 1) : d246648 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246649 q = 1) : d251240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246649, d251240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246649, d251240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246650 q = 1) : d251241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246650, d251241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246650, d251241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246651 q = 1) : d251242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246651, d251242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246651, d251242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246652 q = 1) : d251243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246652, d251243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246652, d251243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25733 (p : Pattern) (selected : d246669 p = 1) : d251249 p = 1 := by
  have h0 (q : Pattern) (selected : d246395 q = 1) : d246395 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246514 q = 1) : d251227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246514, d251227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25720 q selected
    | true =>
      simp only [d246514, d251227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25723 q selected
  have h2 (q : Pattern) (selected : d246527 q = 1) : d246527 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246528 q = 1) : d251228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246528, d251228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246528, d251228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246529 q = 1) : d251229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246529, d251229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246529, d251229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246530 q = 1) : d251230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246530, d251230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246530, d251230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246534 q = 1) : d251234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246534, d251234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246534, d251234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25724 q selected
  have h8 (q : Pattern) (selected : d246536 q = 1) : d246536 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d246537 q = 1) : d251235 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246537, d251235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246537, d251235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246538 q = 1) : d251236 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246538, d251236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246538, d251236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d246539 q = 1) : d251237 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246539, d251237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246539, d251237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d246540 q = 1) : d251238 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246540, d251238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246540, d251238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d246653 q = 1) : d251244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d246653, d251244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246653, d251244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25732 q selected
  have h14 (q : Pattern) (selected : d246664 q = 1) : d246664 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d246665 q = 1) : d251245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d246665, d251245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246665, d251245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246666 q = 1) : d251246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d246666, d251246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d246666, d251246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d246667 q = 1) : d251247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d246667, d251247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d246667, d251247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d246668 q = 1) : d251248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d246668, d251248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d246668, d251248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d246669 q = 1) : d251249 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d246669, d251249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d246669, d251249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro25734 (p : Pattern) (selected : d246675 p = 1) : d251255 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246670 q = 1) : d251250 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d246670, d251250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246670, d251250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25733 q selected
  have h2 (q : Pattern) (selected : d246671 q = 1) : d251251 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d246671, d251251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246671, d251251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246672 q = 1) : d251252 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d246672, d251252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246672, d251252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246673 q = 1) : d251253 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d246673, d251253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246673, d251253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246674 q = 1) : d251254 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d246674, d251254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246674, d251254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246675 q = 1) : d251255 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d246675, d251255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246675, d251255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25735 (p : Pattern) (selected : d10198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1695 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro106 q selected
    | true =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro107 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h3 (q : Pattern) (selected : d1697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10197 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10198 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro25736 (p : Pattern) (selected : d10208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro110 q selected
    | true =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro111 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1715 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h3 (q : Pattern) (selected : d1716 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10184 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6854 q selected
    | true =>
      simp only [d10184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10185 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10205 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1720 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d1721 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d10206 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d10207 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10208 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h11 p selected
theorem eqIntro25737 (p : Pattern) (selected : d246780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246772 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25735 q selected
    | true =>
      simp only [d246772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246773 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246774 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246775 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246776 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25736 q selected
    | true =>
      simp only [d246776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246777 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246778 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246779 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246780 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro25738 (p : Pattern) (selected : d246781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246776 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25736 q selected
    | true =>
      simp only [d246776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246777 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246778 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246779 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246781 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25739 (p : Pattern) (selected : d10253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1746 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
  have h2 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h3 (q : Pattern) (selected : d1747 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1764 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
    | true =>
      simp only [d10249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10251 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10252 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10253 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25740 (p : Pattern) (selected : d246789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246785 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d246785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25739 q selected
    | true =>
      simp only [d246785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246786 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246787 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d246787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246788 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d246788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246789 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d246789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro25741 (p : Pattern) (selected : d246796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246782 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25737 q selected
    | true =>
      simp only [d246782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25738 q selected
  have h2 (q : Pattern) (selected : d246783 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246784 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25738 q selected
    | true =>
      simp only [d246790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25740 q selected
  have h5 (q : Pattern) (selected : d246791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246795 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246796 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro25742 (p : Pattern) (selected : d246800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d246790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25738 q selected
    | true =>
      simp only [d246790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25740 q selected
  have h2 (q : Pattern) (selected : d246791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d246791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d246792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246794 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d246794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246799 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d246799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246800 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d246800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25743 (p : Pattern) (selected : d246806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25741 q selected
    | true =>
      simp only [d246797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25742 q selected
    | true =>
      simp only [d246801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246803 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246804 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246805 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246806 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro25744 (p : Pattern) (selected : d246810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25742 q selected
    | true =>
      simp only [d246801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246810 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro25745 (p : Pattern) (selected : d246830 p = 1) : d251263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246744 q = 1) : d246744 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246753 q = 1) : d246753 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246771 q = 1) : d246771 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d246811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25743 q selected
    | true =>
      simp only [d246811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25744 q selected
  have h5 (q : Pattern) (selected : d246812 q = 1) : d251259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246812, d251259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246812, d251259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246826 q = 1) : d246826 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d246827 q = 1) : d251260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246827, d251260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246827, d251260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246828 q = 1) : d251261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246828, d251261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246828, d251261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246829 q = 1) : d251262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246829, d251262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246829, d251262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d246830 q = 1) : d251263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246830, d251263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246830, d251263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro25746 (p : Pattern) (selected : d246844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246797 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25741 q selected
    | true =>
      simp only [d246797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246798 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25742 q selected
    | true =>
      simp only [d246801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246803 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246804 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d246805 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro25747 (p : Pattern) (selected : d246845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d246801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25742 q selected
    | true =>
      simp only [d246801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d246802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d246802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d246807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d246807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d246808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d246808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d246809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d246809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d246845 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d246845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d246845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro25748 (p : Pattern) (selected : d246854 p = 1) : d251268 p = 1 := by
  have h0 (q : Pattern) (selected : d246744 q = 1) : d246744 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246753 q = 1) : d246753 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246771 q = 1) : d246771 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d246811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25743 q selected
    | true =>
      simp only [d246811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25744 q selected
  have h4 (q : Pattern) (selected : d246812 q = 1) : d251259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246812, d251259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d246812, d251259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d246826 q = 1) : d246826 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d246827 q = 1) : d251260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246827, d251260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d246827, d251260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246828 q = 1) : d251261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246828, d251261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246828, d251261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246829 q = 1) : d251262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246829, d251262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246829, d251262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d246836 q = 1) : d246836 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d246841 q = 1) : d246841 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d246843 q = 1) : d246843 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d246846 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25746 q selected
    | true =>
      simp only [d246846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25747 q selected
  have h13 (q : Pattern) (selected : d246847 q = 1) : d251264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246847, d251264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d246847, d251264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d246850 q = 1) : d246850 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d246851 q = 1) : d251265 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246851, d251265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d246851, d251265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d246852 q = 1) : d251266 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246852, d251266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d246852, d251266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d246853 q = 1) : d251267 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246853, d251267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d246853, d251267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d246854 q = 1) : d251268 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246854, d251268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246854, d251268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro25749 (p : Pattern) (selected : d246874 p = 1) : d251275 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d246843 q = 1) : d246843 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d246846 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d246846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25746 q selected
    | true =>
      simp only [d246846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25747 q selected
  have h3 (q : Pattern) (selected : d246847 q = 1) : d251264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d246847, d251264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246847, d251264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d246850 q = 1) : d246850 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d246851 q = 1) : d251265 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d246851, d251265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d246851, d251265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d246872 q = 1) : d251273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d246872, d251273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246872, d251273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d246873 q = 1) : d251274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d246873, d251274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246873, d251274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d246874 q = 1) : d251275 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d246874, d251275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d246874, d251275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
