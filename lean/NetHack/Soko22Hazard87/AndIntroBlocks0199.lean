import NetHack.Soko22Hazard87.AndIntroBlocks0198
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro49750 (p : Pattern) (ha : d123225 p = 1) (hb : d170946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123079 q = 1) (hb : d170055 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123079, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49744 q ha hb
    | true =>
      simp only [d123079, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49745 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123098 q = 1) (hb : d170056 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123098, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123098, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123099 q = 1) (hb : d170919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123099, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123099, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123100 q = 1) (hb : d170920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123100, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123100, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123104 q = 1) (hb : d170922 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123104, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123104, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49746 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123106 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123107 q = 1) (hb : d170923 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123107, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123107, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123108 q = 1) (hb : d170924 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123108, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123108, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123109 q = 1) (hb : d170925 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123109, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123109, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123110 q = 1) (hb : d170926 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123110, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123110, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123213 q = 1) (hb : d170941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123213, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123213, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49749 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123220 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123221 q = 1) (hb : d170942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123221, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123221, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123222 q = 1) (hb : d170943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123222, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123222, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123223 q = 1) (hb : d170944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123223, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123223, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123224 q = 1) (hb : d170945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123224, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123224, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123225 q = 1) (hb : d170946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123225, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123225, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49751 (p : Pattern) (ha : d123231 p = 1) (hb : d170952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123226 q = 1) (hb : d170947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123226, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123226, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49750 q ha hb
  have h2 (q : Pattern) (ha : d123227 q = 1) (hb : d170948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123227, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123227, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123228 q = 1) (hb : d170949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123228, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123228, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123229 q = 1) (hb : d170950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123229, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123229, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123230 q = 1) (hb : d170951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123230, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123230, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123231 q = 1) (hb : d170952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123231, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123231, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49752 (p : Pattern) (ha : d123363 p = 1) (hb : d170310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123303 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123344 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d123277 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49584 q ha hb
    | true =>
      simp only [d123277, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49585 q ha hb
  have h5 (q : Pattern) (ha : d123345 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123345, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123359 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123360 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123360, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123361 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123361, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123362 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123362, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123363 q = 1) (hb : d170310 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123363, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123363, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49753 (p : Pattern) (ha : d123385 p = 1) (hb : d170320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123303 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123277 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123277, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49584 q ha hb
    | true =>
      simp only [d123277, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49585 q ha hb
  have h4 (q : Pattern) (ha : d123345 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123345, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123345, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123359 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123360 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123360, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123360, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123361 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123361, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123361, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123362 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123362, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123362, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123369 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123374 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123287 q = 1) (hb : d170315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123287, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49587 q ha hb
    | true =>
      simp only [d123287, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49588 q ha hb
  have h13 (q : Pattern) (ha : d123378 q = 1) (hb : d170316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123378, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123382 q = 1) (hb : d170317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123382, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123383 q = 1) (hb : d170318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123383, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123383, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123384 q = 1) (hb : d170319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123384, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123384, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123385 q = 1) (hb : d170320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123385, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123385, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49754 (p : Pattern) (ha : d123410 p = 1) (hb : d170958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123287 q = 1) (hb : d170315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123287, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49587 q ha hb
    | true =>
      simp only [d123287, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49588 q ha hb
  have h3 (q : Pattern) (ha : d123378 q = 1) (hb : d170316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123378, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123378, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123382 q = 1) (hb : d170317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123382, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123382, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123408 q = 1) (hb : d170318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123408, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123408, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123409 q = 1) (hb : d170319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123409, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123409, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123410 q = 1) (hb : d170958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123410, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123410, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49755 (p : Pattern) (ha : d123489 p = 1) (hb : d170965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123448 q = 1) (hb : d170459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123448, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49616 q ha hb
    | true =>
      simp only [d123448, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
  have h2 (q : Pattern) (ha : d123449 q = 1) (hb : d170460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123449, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123449, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123450 q = 1) (hb : d170461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123450, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123450, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123457 q = 1) (hb : d170462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123457, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
    | true =>
      simp only [d123457, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48946 q hb ha
  have h5 (q : Pattern) (ha : d123458 q = 1) (hb : d170463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123458, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123458, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123459 q = 1) (hb : d170464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123459, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123459, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123460 q = 1) (hb : d170465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123460, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123460, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123475 q = 1) (hb : d170479 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123475, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49618 q ha hb
    | true =>
      simp only [d123475, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48919 q hb ha
  have h9 (q : Pattern) (ha : d123476 q = 1) (hb : d170480 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123476, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123476, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123477 q = 1) (hb : d170481 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123477, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123477, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123478 q = 1) (hb : d170482 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123478, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123478, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123488 q = 1) (hb : d170964 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123488, d170964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123488, d170964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123489 q = 1) (hb : d170965 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123489, d170965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123489, d170965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49756 (p : Pattern) (ha : d123495 p = 1) (hb : d170971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123490 q = 1) (hb : d170966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123490, d170966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49755 q ha hb
    | true =>
      simp only [d123490, d170966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123491 q = 1) (hb : d170967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123491, d170967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123491, d170967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123481 q = 1) (hb : d170485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123481, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49622 q ha hb
    | true =>
      simp only [d123481, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123482 q = 1) (hb : d170486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123482, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123482, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123492 q = 1) (hb : d170968 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123492, d170968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123492, d170968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123493 q = 1) (hb : d170969 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123493, d170969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123493, d170969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123494 q = 1) (hb : d170970 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123494, d170970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123494, d170970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123495 q = 1) (hb : d170971 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123495, d170971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123495, d170971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49757 (p : Pattern) (ha : d123519 p = 1) (hb : d170977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123500 q = 1) (hb : d170972 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123500, d170972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49756 q ha hb
    | true =>
      simp only [d123500, d170972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49627 q ha hb
  have h3 (q : Pattern) (ha : d123501 q = 1) (hb : d170973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123501, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123501, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123516 q = 1) (hb : d170974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123516, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123516, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123517 q = 1) (hb : d170975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123517, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123517, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123518 q = 1) (hb : d170976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123518, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123518, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123519 q = 1) (hb : d170977 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123519, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123519, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49758 (p : Pattern) (ha : d123532 p = 1) (hb : d170983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123295 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123386 q = 1) (hb : d170321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123386, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49752 q ha hb
    | true =>
      simp only [d123386, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49753 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123405 q = 1) (hb : d170322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123405, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123405, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123406 q = 1) (hb : d170956 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123406, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123406, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123407 q = 1) (hb : d170957 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123407, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123407, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123411 q = 1) (hb : d170959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123411, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123411, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49754 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123413 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123414 q = 1) (hb : d170960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123414, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123414, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123415 q = 1) (hb : d170961 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123415, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123415, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123416 q = 1) (hb : d170962 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123416, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123416, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123417 q = 1) (hb : d170963 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123417, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123417, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123520 q = 1) (hb : d170978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123520, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123520, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49757 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123527 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123528 q = 1) (hb : d170979 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123528, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123528, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123529 q = 1) (hb : d170980 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123529, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123529, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123530 q = 1) (hb : d170981 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123530, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123530, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123531 q = 1) (hb : d170982 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123531, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123531, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123532 q = 1) (hb : d170983 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123532, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123532, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49759 (p : Pattern) (ha : d123538 p = 1) (hb : d170989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123533 q = 1) (hb : d170984 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123533, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123533, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49758 q ha hb
  have h2 (q : Pattern) (ha : d123534 q = 1) (hb : d170985 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123534, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123534, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123535 q = 1) (hb : d170986 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123535, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123535, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123536 q = 1) (hb : d170987 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123536, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123536, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123537 q = 1) (hb : d170988 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123537, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123537, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123538 q = 1) (hb : d170989 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123538, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123538, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49760 (p : Pattern) (ha : d123665 p = 1) (hb : d170574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123618 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123646 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d123583 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49635 q ha hb
    | true =>
      simp only [d123583, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49636 q ha hb
  have h5 (q : Pattern) (ha : d123647 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123647, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123661 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d123662 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123662, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d123663 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123663, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123664 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123664, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123665 q = 1) (hb : d170574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123665, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123665, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49761 (p : Pattern) (ha : d123687 p = 1) (hb : d170584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123609 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123618 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123646 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123583 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123583, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49635 q ha hb
    | true =>
      simp only [d123583, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49636 q ha hb
  have h4 (q : Pattern) (ha : d123647 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123647, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d123647, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123661 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d123662 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123662, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123662, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123663 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123663, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123663, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123664 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123664, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123664, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123676 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123679 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123593 q = 1) (hb : d170579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123593, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49638 q ha hb
    | true =>
      simp only [d123593, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49639 q ha hb
  have h13 (q : Pattern) (ha : d123680 q = 1) (hb : d170580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d123680, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123683 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123684 q = 1) (hb : d170581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123684, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123685 q = 1) (hb : d170582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123685, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123685, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d123686 q = 1) (hb : d170583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123686, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123686, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d123687 q = 1) (hb : d170584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123687, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d123687, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49762 (p : Pattern) (ha : d123712 p = 1) (hb : d170996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123679 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123593 q = 1) (hb : d170579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123593, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49638 q ha hb
    | true =>
      simp only [d123593, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49639 q ha hb
  have h3 (q : Pattern) (ha : d123680 q = 1) (hb : d170580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123680, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123680, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123683 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123684 q = 1) (hb : d170581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123684, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123684, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123710 q = 1) (hb : d170582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123710, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123710, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123711 q = 1) (hb : d170583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123711, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123711, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123712 q = 1) (hb : d170996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123712, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123712, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49763 (p : Pattern) (ha : d123781 p = 1) (hb : d171003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123740 q = 1) (hb : d170716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123740, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49665 q ha hb
    | true =>
      simp only [d123740, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
  have h2 (q : Pattern) (ha : d123741 q = 1) (hb : d170717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123741, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123741, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123742 q = 1) (hb : d170718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123742, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123742, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123749 q = 1) (hb : d170719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123749, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
    | true =>
      simp only [d123749, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49001 q hb ha
  have h5 (q : Pattern) (ha : d123750 q = 1) (hb : d170720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123750, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123750, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123751 q = 1) (hb : d170721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123751, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123751, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123752 q = 1) (hb : d170722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123752, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123752, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123767 q = 1) (hb : d170736 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d123767, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49667 q ha hb
    | true =>
      simp only [d123767, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48974 q hb ha
  have h9 (q : Pattern) (ha : d123768 q = 1) (hb : d170737 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d123768, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123768, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123769 q = 1) (hb : d170738 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d123769, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123769, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123770 q = 1) (hb : d170739 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d123770, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123770, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d123780 q = 1) (hb : d171002 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123780, d171002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123780, d171002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123781 q = 1) (hb : d171003 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123781, d171003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123781, d171003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49764 (p : Pattern) (ha : d123787 p = 1) (hb : d171009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123782 q = 1) (hb : d171004 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123782, d171004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49763 q ha hb
    | true =>
      simp only [d123782, d171004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123783 q = 1) (hb : d171005 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123783, d171005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123783, d171005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123773 q = 1) (hb : d170742 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123773, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49671 q ha hb
    | true =>
      simp only [d123773, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123774 q = 1) (hb : d170743 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123774, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123774, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123784 q = 1) (hb : d171006 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123784, d171006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123784, d171006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123785 q = 1) (hb : d171007 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123785, d171007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123785, d171007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123786 q = 1) (hb : d171008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123786, d171008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123786, d171008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123787 q = 1) (hb : d171009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123787, d171009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123787, d171009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49765 (p : Pattern) (ha : d123811 p = 1) (hb : d171015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123792 q = 1) (hb : d171010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123792, d171010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49764 q ha hb
    | true =>
      simp only [d123792, d171010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49676 q ha hb
  have h3 (q : Pattern) (ha : d123793 q = 1) (hb : d171011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123793, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123793, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123808 q = 1) (hb : d171012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123808, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123808, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123809 q = 1) (hb : d171013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123809, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123809, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123810 q = 1) (hb : d171014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123810, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123810, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123811 q = 1) (hb : d171015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123811, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123811, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49766 (p : Pattern) (ha : d123824 p = 1) (hb : d171021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123688 q = 1) (hb : d170585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123688, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49760 q ha hb
    | true =>
      simp only [d123688, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49761 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123706 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d123707 q = 1) (hb : d170586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123707, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123707, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123708 q = 1) (hb : d170994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123708, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123708, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123709 q = 1) (hb : d170995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123709, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123709, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123713 q = 1) (hb : d170997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123713, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123713, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49762 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123715 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123716 q = 1) (hb : d170998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123716, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123716, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123717 q = 1) (hb : d170999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123717, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123717, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123718 q = 1) (hb : d171000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123718, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123718, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123719 q = 1) (hb : d171001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123719, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123719, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123812 q = 1) (hb : d171016 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123812, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123812, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49765 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123819 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123820 q = 1) (hb : d171017 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123820, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123820, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123821 q = 1) (hb : d171018 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123821, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123821, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123822 q = 1) (hb : d171019 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123822, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123822, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123823 q = 1) (hb : d171020 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123823, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123823, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123824 q = 1) (hb : d171021 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123824, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123824, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49767 (p : Pattern) (ha : d123830 p = 1) (hb : d171027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123825 q = 1) (hb : d171022 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123825, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123825, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49766 q ha hb
  have h2 (q : Pattern) (ha : d123826 q = 1) (hb : d171023 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123826, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123826, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123827 q = 1) (hb : d171024 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123827, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123827, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123828 q = 1) (hb : d171025 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123828, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123828, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123829 q = 1) (hb : d171026 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123829, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123829, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123830 q = 1) (hb : d171027 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123830, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123830, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49768 (p : Pattern) (ha : d123836 p = 1) (hb : d171033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d122703 q = 1) (hb : d170890 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122703, d170890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49731 q ha hb
    | true =>
      simp only [d122703, d170890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49737 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122926 q = 1) (hb : d170917 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122926, d170917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122926, d170917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49743 q ha hb
  have h3 (q : Pattern) (ha : d122927 q = 1) (hb : d170918 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d122927, d170918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d122927, d170918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123232 q = 1) (hb : d170953 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123232, d170953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123232, d170953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49751 q ha hb
  have h5 (q : Pattern) (ha : d123233 q = 1) (hb : d170954 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123233, d170954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123233, d170954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123234 q = 1) (hb : d170955 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123234, d170955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123234, d170955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123539 q = 1) (hb : d170990 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123539, d170990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123539, d170990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49759 q ha hb
  have h8 (q : Pattern) (ha : d123540 q = 1) (hb : d170991 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123540, d170991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123540, d170991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123541 q = 1) (hb : d170992 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123541, d170992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123541, d170992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123542 q = 1) (hb : d170993 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123542, d170993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123542, d170993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123831 q = 1) (hb : d171028 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123831, d171028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123831, d171028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49767 q ha hb
  have h12 (q : Pattern) (ha : d123832 q = 1) (hb : d171029 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123832, d171029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123832, d171029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123833 q = 1) (hb : d171030 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123833, d171030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123833, d171030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123834 q = 1) (hb : d171031 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123834, d171031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123834, d171031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123835 q = 1) (hb : d171032 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d123835, d171032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123835, d171032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123836 q = 1) (hb : d171033 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d123836, d171033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123836, d171033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro49769 (p : Pattern) (ha : d123842 p = 1) (hb : d171039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123837 q = 1) (hb : d171034 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d123837, d171034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49768 q ha hb
    | true =>
      simp only [d123837, d171034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123838 q = 1) (hb : d171035 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d123838, d171035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123838, d171035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123839 q = 1) (hb : d171036 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d123839, d171036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123839, d171036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123840 q = 1) (hb : d171037 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d123840, d171037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123840, d171037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123841 q = 1) (hb : d171038 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d123841, d171038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123841, d171038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123842 q = 1) (hb : d171039 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d123842, d171039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123842, d171039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49770 (p : Pattern) (ha : d123848 p = 1) (hb : d171045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123843 q = 1) (hb : d171040 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d123843, d171040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49769 q ha hb
    | true =>
      simp only [d123843, d171040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123844 q = 1) (hb : d171041 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d123844, d171041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123844, d171041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123845 q = 1) (hb : d171042 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d123845, d171042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123845, d171042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123846 q = 1) (hb : d171043 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d123846, d171043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123846, d171043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123847 q = 1) (hb : d171044 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d123847, d171044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123847, d171044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123848 q = 1) (hb : d171045 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d123848, d171045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123848, d171045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49771 (p : Pattern) (ha : d123854 p = 1) (hb : d171051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123849 q = 1) (hb : d171046 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d123849, d171046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49770 q ha hb
    | true =>
      simp only [d123849, d171046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123850 q = 1) (hb : d171047 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d123850, d171047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123850, d171047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123851 q = 1) (hb : d171048 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d123851, d171048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123851, d171048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123852 q = 1) (hb : d171049 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d123852, d171049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123852, d171049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123853 q = 1) (hb : d171050 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d123853, d171050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123853, d171050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123854 q = 1) (hb : d171051 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d123854, d171051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123854, d171051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49772 (p : Pattern) (ha : d123860 p = 1) (hb : d171057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123855 q = 1) (hb : d171052 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d123855, d171052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49771 q ha hb
    | true =>
      simp only [d123855, d171052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123856 q = 1) (hb : d171053 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d123856, d171053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123856, d171053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123857 q = 1) (hb : d171054 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d123857, d171054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123857, d171054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123858 q = 1) (hb : d171055 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d123858, d171055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123858, d171055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123859 q = 1) (hb : d171056 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d123859, d171056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123859, d171056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123860 q = 1) (hb : d171057 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d123860, d171057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123860, d171057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49773 (p : Pattern) (ha : d123866 p = 1) (hb : d171063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123861 q = 1) (hb : d171058 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d123861, d171058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49772 q ha hb
    | true =>
      simp only [d123861, d171058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123862 q = 1) (hb : d171059 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d123862, d171059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123862, d171059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123863 q = 1) (hb : d171060 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d123863, d171060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123863, d171060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123864 q = 1) (hb : d171061 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d123864, d171061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123864, d171061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123865 q = 1) (hb : d171062 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d123865, d171062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123865, d171062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123866 q = 1) (hb : d171063 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d123866, d171063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123866, d171063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49774 (p : Pattern) (ha : d123872 p = 1) (hb : d171069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123867 q = 1) (hb : d171064 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d123867, d171064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49773 q ha hb
    | true =>
      simp only [d123867, d171064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123868 q = 1) (hb : d171065 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d123868, d171065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123868, d171065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123869 q = 1) (hb : d171066 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d123869, d171066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123869, d171066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123870 q = 1) (hb : d171067 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d123870, d171067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123870, d171067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123871 q = 1) (hb : d171068 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d123871, d171068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123871, d171068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123872 q = 1) (hb : d171069 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d123872, d171069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123872, d171069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49775 (p : Pattern) (ha : d123878 p = 1) (hb : d171075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123873 q = 1) (hb : d171070 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d123873, d171070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49774 q ha hb
    | true =>
      simp only [d123873, d171070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123874 q = 1) (hb : d171071 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d123874, d171071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123874, d171071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123875 q = 1) (hb : d171072 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d123875, d171072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123875, d171072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123876 q = 1) (hb : d171073 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d123876, d171073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123876, d171073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123877 q = 1) (hb : d171074 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d123877, d171074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123877, d171074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123878 q = 1) (hb : d171075 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d123878, d171075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123878, d171075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49776 (p : Pattern) (ha : d125455 p = 1) (hb : d169470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14076 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14092 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125451 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125451, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14114 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125452 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125452, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125453 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125453, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125454 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125454, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125455 q = 1) (hb : d169470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125455, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125455, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49777 (p : Pattern) (ha : d125460 p = 1) (hb : d169477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14070 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14076 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125451 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125451, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14114 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125452 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125452, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125453 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125453, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125454 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125454, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14123 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14127 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14129 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125456 q = 1) (hb : d169473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125456, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125457 q = 1) (hb : d169474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125457, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125458 q = 1) (hb : d169475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125458, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125458, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125459 q = 1) (hb : d169476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125459, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125459, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125460 q = 1) (hb : d169477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125460, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125460, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49778 (p : Pattern) (ha : d125467 p = 1) (hb : d170841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125456 q = 1) (hb : d169473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125456, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14135 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125457 q = 1) (hb : d169474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125457, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125465 q = 1) (hb : d169475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125465, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125465, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125466 q = 1) (hb : d169476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125466, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125466, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125467 q = 1) (hb : d170841 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125467, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125467, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49779 (p : Pattern) (ha : d125477 p = 1) (hb : d170851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d169449 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125473 q = 1) (hb : d170847 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125473, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125473, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14191 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125474 q = 1) (hb : d170848 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125474, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125474, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125475 q = 1) (hb : d170849 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125475, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125475, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125476 q = 1) (hb : d170850 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125476, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125476, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125477 q = 1) (hb : d170851 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125477, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125477, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49780 (p : Pattern) (ha : d125483 p = 1) (hb : d170857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14064 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125461 q = 1) (hb : d169478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125461, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49776 q ha hb
    | true =>
      simp only [d125461, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49777 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125462 q = 1) (hb : d169479 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125462, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125462, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125463 q = 1) (hb : d170839 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125463, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125463, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125464 q = 1) (hb : d170840 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125464, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125464, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125468 q = 1) (hb : d170842 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125468, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125468, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49778 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125469 q = 1) (hb : d170843 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125469, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125469, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125470 q = 1) (hb : d170844 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125470, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125470, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125471 q = 1) (hb : d170845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125471, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125471, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125472 q = 1) (hb : d170846 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125472, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125472, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125478 q = 1) (hb : d170852 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125478, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125478, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49779 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125479 q = 1) (hb : d170853 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125479, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125479, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125480 q = 1) (hb : d170854 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125480, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125480, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125481 q = 1) (hb : d170855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125481, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125481, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125482 q = 1) (hb : d170856 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125482, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125482, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125483 q = 1) (hb : d170857 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125483, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125483, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49781 (p : Pattern) (ha : d125489 p = 1) (hb : d170863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d125446 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22508 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d125447 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d125448 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d125449 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d125450 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125484 q = 1) (hb : d170858 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125484, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125484, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49780 q ha hb
  have h8 (q : Pattern) (ha : d125485 q = 1) (hb : d170859 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125485, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125485, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125486 q = 1) (hb : d170860 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125486, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125486, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125487 q = 1) (hb : d170861 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125487, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125487, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125488 q = 1) (hb : d170862 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125488, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125488, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d125489 q = 1) (hb : d170863 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125489, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d125489, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro49782 (p : Pattern) (ha : d125494 p = 1) (hb : d169612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14251 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14260 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14280 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125490 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125490, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14314 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125491 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125491, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125492 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125492, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125493 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125493, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125494 q = 1) (hb : d169612 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125494, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125494, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49783 (p : Pattern) (ha : d125499 p = 1) (hb : d169622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14251 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14260 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14280 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125490 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125490, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125491 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125491, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125492 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125492, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125493 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125493, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14324 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d169617 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125495 q = 1) (hb : d169618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125495, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14338 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125496 q = 1) (hb : d169619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125496, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125497 q = 1) (hb : d169620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125497, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125497, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125498 q = 1) (hb : d169621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125498, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125498, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125499 q = 1) (hb : d169622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125499, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125499, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49784 (p : Pattern) (ha : d125506 p = 1) (hb : d170866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d169617 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125495 q = 1) (hb : d169618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125495, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14338 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125496 q = 1) (hb : d169619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125496, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125504 q = 1) (hb : d169620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125504, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125504, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125505 q = 1) (hb : d169621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125505, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125505, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125506 q = 1) (hb : d170866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125506, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125506, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49785 (p : Pattern) (ha : d125516 p = 1) (hb : d170877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d170872 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125512 q = 1) (hb : d170873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125512, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125512, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14438 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125513 q = 1) (hb : d170874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125513, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125513, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125514 q = 1) (hb : d170875 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125514, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125514, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125515 q = 1) (hb : d170876 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125515, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125515, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125516 q = 1) (hb : d170877 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125516, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125516, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49786 (p : Pattern) (ha : d125522 p = 1) (hb : d170883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14243 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125500 q = 1) (hb : d169623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125500, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49782 q ha hb
    | true =>
      simp only [d125500, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49783 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125501 q = 1) (hb : d169624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125501, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125501, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125502 q = 1) (hb : d170864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125502, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125502, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125503 q = 1) (hb : d170865 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125503, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125503, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125507 q = 1) (hb : d170867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125507, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125507, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49784 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14365 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125508 q = 1) (hb : d170868 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125508, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125508, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125509 q = 1) (hb : d170869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125509, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125509, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125510 q = 1) (hb : d170870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125510, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125510, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125511 q = 1) (hb : d170871 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125511, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125511, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125517 q = 1) (hb : d170878 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125517, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125517, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49785 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14454 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125518 q = 1) (hb : d170879 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125518, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125518, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125519 q = 1) (hb : d170880 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125519, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125519, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125520 q = 1) (hb : d170881 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125520, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125520, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125521 q = 1) (hb : d170882 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125521, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125521, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125522 q = 1) (hb : d170883 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125522, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125522, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49787 (p : Pattern) (ha : d125528 p = 1) (hb : d170889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125523 q = 1) (hb : d170884 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125523, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125523, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49786 q ha hb
  have h2 (q : Pattern) (ha : d125524 q = 1) (hb : d170885 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125524, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125524, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125525 q = 1) (hb : d170886 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125525, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125525, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125526 q = 1) (hb : d170887 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125526, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125526, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125527 q = 1) (hb : d170888 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125527, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125527, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125528 q = 1) (hb : d170889 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125528, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125528, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49788 (p : Pattern) (ha : d125534 p = 1) (hb : d169820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14549 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125530 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125530, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14587 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125531 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125531, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125532 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125532, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125533 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125533, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125534 q = 1) (hb : d169820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125534, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125534, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49789 (p : Pattern) (ha : d125539 p = 1) (hb : d169830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125530 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125530, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125531 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125531, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125532 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125532, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125533 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125533, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14602 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14604 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d169825 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125535 q = 1) (hb : d169826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125535, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14611 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125536 q = 1) (hb : d169827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125536, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125537 q = 1) (hb : d169828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125537, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125537, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125538 q = 1) (hb : d169829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125538, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125538, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125539 q = 1) (hb : d169830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125539, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125539, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49790 (p : Pattern) (ha : d125546 p = 1) (hb : d170893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14604 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d169825 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125535 q = 1) (hb : d169826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125535, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14611 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125536 q = 1) (hb : d169827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125536, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125544 q = 1) (hb : d169828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125544, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125544, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125545 q = 1) (hb : d169829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125545, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125545, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125546 q = 1) (hb : d170893 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125546, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125546, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49791 (p : Pattern) (ha : d125556 p = 1) (hb : d170904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d170899 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125552 q = 1) (hb : d170900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125552, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125552, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14727 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125553 q = 1) (hb : d170901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125553, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125553, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125554 q = 1) (hb : d170902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125554, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125554, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125555 q = 1) (hb : d170903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125555, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125555, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125556 q = 1) (hb : d170904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125556, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125556, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49792 (p : Pattern) (ha : d125562 p = 1) (hb : d170910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125540 q = 1) (hb : d169831 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125540, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49788 q ha hb
    | true =>
      simp only [d125540, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49789 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125541 q = 1) (hb : d169832 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125541, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125541, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125542 q = 1) (hb : d170891 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125542, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125542, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125543 q = 1) (hb : d170892 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125543, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125543, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125547 q = 1) (hb : d170894 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125547, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125547, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49790 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14638 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125548 q = 1) (hb : d170895 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125548, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125548, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125549 q = 1) (hb : d170896 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125549, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125549, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125550 q = 1) (hb : d170897 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125550, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125550, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125551 q = 1) (hb : d170898 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125551, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125551, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125557 q = 1) (hb : d170905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125557, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125557, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49791 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14743 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125558 q = 1) (hb : d170906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125558, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125558, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125559 q = 1) (hb : d170907 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125559, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125559, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125560 q = 1) (hb : d170908 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125560, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125560, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125561 q = 1) (hb : d170909 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125561, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125561, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125562 q = 1) (hb : d170910 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125562, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125562, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49793 (p : Pattern) (ha : d125568 p = 1) (hb : d170916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125563 q = 1) (hb : d170911 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125563, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125563, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49792 q ha hb
  have h2 (q : Pattern) (ha : d125564 q = 1) (hb : d170912 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125564, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125564, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125565 q = 1) (hb : d170913 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125565, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125565, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125566 q = 1) (hb : d170914 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125566, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125566, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125567 q = 1) (hb : d170915 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125567, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125567, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125568 q = 1) (hb : d170916 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125568, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125568, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49794 (p : Pattern) (ha : d125575 p = 1) (hb : d170044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14866 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125571 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125571, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14924 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125572 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125572, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125573 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125573, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125574 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125574, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125575 q = 1) (hb : d170044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125575, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125575, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49795 (p : Pattern) (ha : d125580 p = 1) (hb : d170054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125571 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125571, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14924 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125572 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125572, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125573 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125573, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125574 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125574, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14934 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14939 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14942 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d170049 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125576 q = 1) (hb : d170050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125576, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14949 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125577 q = 1) (hb : d170051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125577, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125578 q = 1) (hb : d170052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125578, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125578, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125579 q = 1) (hb : d170053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125579, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125579, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125580 q = 1) (hb : d170054 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125580, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125580, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49796 (p : Pattern) (ha : d125587 p = 1) (hb : d170921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d170049 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125576 q = 1) (hb : d170050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125576, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14949 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125577 q = 1) (hb : d170051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125577, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125585 q = 1) (hb : d170052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125585, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125585, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125586 q = 1) (hb : d170053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125586, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125586, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125587 q = 1) (hb : d170921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125587, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125587, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49797 (p : Pattern) (ha : d125597 p = 1) (hb : d170940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d170935 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125593 q = 1) (hb : d170936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125593, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125593, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125594 q = 1) (hb : d170937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125594, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125594, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125595 q = 1) (hb : d170938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125595, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125595, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125596 q = 1) (hb : d170939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125596, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125596, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125597 q = 1) (hb : d170940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125597, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125597, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49798 (p : Pattern) (ha : d125603 p = 1) (hb : d170946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14817 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125581 q = 1) (hb : d170055 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125581, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49794 q ha hb
    | true =>
      simp only [d125581, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49795 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14972 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125582 q = 1) (hb : d170056 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125582, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125582, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125583 q = 1) (hb : d170919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125583, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125583, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125584 q = 1) (hb : d170920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125584, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125584, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125588 q = 1) (hb : d170922 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125588, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125588, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49796 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14981 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125589 q = 1) (hb : d170923 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125589, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125589, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125590 q = 1) (hb : d170924 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125590, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125590, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125591 q = 1) (hb : d170925 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125591, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125591, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125592 q = 1) (hb : d170926 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125592, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125592, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125598 q = 1) (hb : d170941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125598, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125598, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49797 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125599 q = 1) (hb : d170942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125599, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125599, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125600 q = 1) (hb : d170943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125600, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125600, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125601 q = 1) (hb : d170944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125601, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125601, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125602 q = 1) (hb : d170945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125602, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125602, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125603 q = 1) (hb : d170946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125603, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125603, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49799 (p : Pattern) (ha : d125609 p = 1) (hb : d170952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125604 q = 1) (hb : d170947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125604, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125604, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49798 q ha hb
  have h2 (q : Pattern) (ha : d125605 q = 1) (hb : d170948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125605, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125605, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125606 q = 1) (hb : d170949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125606, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125606, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125607 q = 1) (hb : d170950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125607, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125607, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125608 q = 1) (hb : d170951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125608, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125608, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125609 q = 1) (hb : d170952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125609, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125609, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49800 (p : Pattern) (ha : d125617 p = 1) (hb : d170310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15218 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15259 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125613 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125613, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125614 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125614, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125615 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125615, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125616 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125616, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125617 q = 1) (hb : d170310 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125617, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125617, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49801 (p : Pattern) (ha : d125622 p = 1) (hb : d170320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15259 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125613 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125613, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125614 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125614, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125615 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125615, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125616 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125616, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d170315 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125618 q = 1) (hb : d170316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125618, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15342 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125619 q = 1) (hb : d170317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125619, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125620 q = 1) (hb : d170318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125620, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125620, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125621 q = 1) (hb : d170319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125621, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125621, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125622 q = 1) (hb : d170320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125622, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125622, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49802 (p : Pattern) (ha : d125629 p = 1) (hb : d170958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d170315 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125618 q = 1) (hb : d170316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125618, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125619 q = 1) (hb : d170317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125619, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125627 q = 1) (hb : d170318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125627, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125627, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125628 q = 1) (hb : d170319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125628, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125628, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125629 q = 1) (hb : d170958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125629, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49803 (p : Pattern) (ha : d125639 p = 1) (hb : d170977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d170972 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125635 q = 1) (hb : d170973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125635, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15512 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125636 q = 1) (hb : d170974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125636, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125637 q = 1) (hb : d170975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125637, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125638 q = 1) (hb : d170976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125638, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125639 q = 1) (hb : d170977 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125639, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49804 (p : Pattern) (ha : d125645 p = 1) (hb : d170983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125623 q = 1) (hb : d170321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125623, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49800 q ha hb
    | true =>
      simp only [d125623, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49801 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15365 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125624 q = 1) (hb : d170322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125624, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125624, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125625 q = 1) (hb : d170956 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125625, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125626 q = 1) (hb : d170957 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125626, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125630 q = 1) (hb : d170959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125630, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49802 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15374 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125631 q = 1) (hb : d170960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125631, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125632 q = 1) (hb : d170961 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125632, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125633 q = 1) (hb : d170962 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125633, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125634 q = 1) (hb : d170963 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125634, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125640 q = 1) (hb : d170978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125640, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49803 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15528 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125641 q = 1) (hb : d170979 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125641, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125642 q = 1) (hb : d170980 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125642, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125643 q = 1) (hb : d170981 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125643, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125644 q = 1) (hb : d170982 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125644, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125645 q = 1) (hb : d170983 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125645, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49805 (p : Pattern) (ha : d125651 p = 1) (hb : d170989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125646 q = 1) (hb : d170984 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125646, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49804 q ha hb
  have h2 (q : Pattern) (ha : d125647 q = 1) (hb : d170985 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125647, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125648 q = 1) (hb : d170986 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125648, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125649 q = 1) (hb : d170987 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125649, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125650 q = 1) (hb : d170988 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125650, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125651 q = 1) (hb : d170989 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125651, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49806 (p : Pattern) (ha : d125660 p = 1) (hb : d170574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15610 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15647 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125656 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125656, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15705 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125657 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125657, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d125658 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125658, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125659 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125659, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125660 q = 1) (hb : d170574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125660, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125660, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49807 (p : Pattern) (ha : d125665 p = 1) (hb : d170584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d125656 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125656, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15705 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d125657 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125657, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d125658 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125658, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125659 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125659, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15715 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15720 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15723 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d170579 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d125661 q = 1) (hb : d170580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125661, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15730 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125662 q = 1) (hb : d170581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125662, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125663 q = 1) (hb : d170582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125663, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125663, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125664 q = 1) (hb : d170583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125664, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125664, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d125665 q = 1) (hb : d170584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125665, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125665, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49808 (p : Pattern) (ha : d125672 p = 1) (hb : d170996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d170579 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125661 q = 1) (hb : d170580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125661, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125662 q = 1) (hb : d170581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125662, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125670 q = 1) (hb : d170582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125670, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125670, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125671 q = 1) (hb : d170583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125671, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125671, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125672 q = 1) (hb : d170996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125672, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49809 (p : Pattern) (ha : d125682 p = 1) (hb : d171015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d171010 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125678 q = 1) (hb : d171011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125678, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125678, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125679 q = 1) (hb : d171012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125679, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125679, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125680 q = 1) (hb : d171013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125680, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125680, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125681 q = 1) (hb : d171014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125681, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125681, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125682 q = 1) (hb : d171015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125682, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125682, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49810 (p : Pattern) (ha : d125688 p = 1) (hb : d171021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125666 q = 1) (hb : d170585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125666, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49806 q ha hb
    | true =>
      simp only [d125666, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49807 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125667 q = 1) (hb : d170586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125667, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125667, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125668 q = 1) (hb : d170994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125668, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125668, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125669 q = 1) (hb : d170995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125669, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125669, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125673 q = 1) (hb : d170997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125673, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125673, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49808 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15762 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125674 q = 1) (hb : d170998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125674, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125674, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125675 q = 1) (hb : d170999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125675, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125675, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125676 q = 1) (hb : d171000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125676, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125676, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125677 q = 1) (hb : d171001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125677, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125677, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125683 q = 1) (hb : d171016 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125683, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125683, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49809 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15906 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125684 q = 1) (hb : d171017 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125684, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125684, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125685 q = 1) (hb : d171018 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125685, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125685, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125686 q = 1) (hb : d171019 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125686, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125686, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125687 q = 1) (hb : d171020 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125687, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125687, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125688 q = 1) (hb : d171021 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125688, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125688, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49811 (p : Pattern) (ha : d125694 p = 1) (hb : d171027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125689 q = 1) (hb : d171022 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125689, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49810 q ha hb
  have h2 (q : Pattern) (ha : d125690 q = 1) (hb : d171023 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125690, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125691 q = 1) (hb : d171024 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125691, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125692 q = 1) (hb : d171025 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125692, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125693 q = 1) (hb : d171026 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125693, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125694 q = 1) (hb : d171027 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125694, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49812 (p : Pattern) (ha : d125700 p = 1) (hb : d171033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d125529 q = 1) (hb : d170890 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, d170890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49781 q ha hb
    | true =>
      simp only [d125529, d170890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49787 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125569 q = 1) (hb : d170917 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, d170917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125569, d170917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49793 q ha hb
  have h3 (q : Pattern) (ha : d125570 q = 1) (hb : d170918 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, d170918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, d170918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125610 q = 1) (hb : d170953 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, d170953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125610, d170953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49799 q ha hb
  have h5 (q : Pattern) (ha : d125611 q = 1) (hb : d170954 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, d170954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125611, d170954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125612 q = 1) (hb : d170955 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, d170955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, d170955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125652 q = 1) (hb : d170990 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, d170990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125652, d170990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49805 q ha hb
  have h8 (q : Pattern) (ha : d125653 q = 1) (hb : d170991 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, d170991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125653, d170991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125654 q = 1) (hb : d170992 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, d170992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125654, d170992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125655 q = 1) (hb : d170993 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, d170993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, d170993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125695 q = 1) (hb : d171028 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, d171028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125695, d171028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49811 q ha hb
  have h12 (q : Pattern) (ha : d125696 q = 1) (hb : d171029 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, d171029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125696, d171029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125697 q = 1) (hb : d171030 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, d171030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125697, d171030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125698 q = 1) (hb : d171031 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, d171031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125698, d171031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125699 q = 1) (hb : d171032 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, d171032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, d171032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125700 q = 1) (hb : d171033 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, d171033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, d171033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro49813 (p : Pattern) (ha : d125706 p = 1) (hb : d171039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125701 q = 1) (hb : d171034 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, d171034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49812 q ha hb
    | true =>
      simp only [d125701, d171034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125702 q = 1) (hb : d171035 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, d171035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, d171035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125703 q = 1) (hb : d171036 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, d171036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, d171036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125704 q = 1) (hb : d171037 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, d171037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, d171037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125705 q = 1) (hb : d171038 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, d171038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, d171038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125706 q = 1) (hb : d171039 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, d171039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, d171039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49814 (p : Pattern) (ha : d125712 p = 1) (hb : d171045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125707 q = 1) (hb : d171040 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, d171040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49813 q ha hb
    | true =>
      simp only [d125707, d171040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125708 q = 1) (hb : d171041 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, d171041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, d171041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125709 q = 1) (hb : d171042 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, d171042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, d171042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125710 q = 1) (hb : d171043 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, d171043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, d171043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125711 q = 1) (hb : d171044 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, d171044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, d171044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125712 q = 1) (hb : d171045 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, d171045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, d171045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49815 (p : Pattern) (ha : d125718 p = 1) (hb : d171051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125713 q = 1) (hb : d171046 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, d171046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49814 q ha hb
    | true =>
      simp only [d125713, d171046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125714 q = 1) (hb : d171047 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, d171047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, d171047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125715 q = 1) (hb : d171048 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, d171048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, d171048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125716 q = 1) (hb : d171049 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, d171049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, d171049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125717 q = 1) (hb : d171050 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, d171050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, d171050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125718 q = 1) (hb : d171051 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, d171051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, d171051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49816 (p : Pattern) (ha : d125724 p = 1) (hb : d171057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125719 q = 1) (hb : d171052 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, d171052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49815 q ha hb
    | true =>
      simp only [d125719, d171052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125720 q = 1) (hb : d171053 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, d171053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, d171053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125721 q = 1) (hb : d171054 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, d171054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, d171054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125722 q = 1) (hb : d171055 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, d171055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, d171055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125723 q = 1) (hb : d171056 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, d171056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, d171056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125724 q = 1) (hb : d171057 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, d171057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, d171057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49817 (p : Pattern) (ha : d125730 p = 1) (hb : d171063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125725 q = 1) (hb : d171058 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, d171058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49816 q ha hb
    | true =>
      simp only [d125725, d171058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125726 q = 1) (hb : d171059 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, d171059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, d171059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125727 q = 1) (hb : d171060 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, d171060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, d171060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125728 q = 1) (hb : d171061 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, d171061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, d171061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125729 q = 1) (hb : d171062 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, d171062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, d171062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125730 q = 1) (hb : d171063 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, d171063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, d171063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49818 (p : Pattern) (ha : d125736 p = 1) (hb : d171069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125731 q = 1) (hb : d171064 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, d171064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49817 q ha hb
    | true =>
      simp only [d125731, d171064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125732 q = 1) (hb : d171065 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, d171065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, d171065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125733 q = 1) (hb : d171066 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, d171066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, d171066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125734 q = 1) (hb : d171067 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, d171067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, d171067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125735 q = 1) (hb : d171068 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, d171068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, d171068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125736 q = 1) (hb : d171069 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, d171069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, d171069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49819 (p : Pattern) (ha : d125742 p = 1) (hb : d171075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125737 q = 1) (hb : d171070 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, d171070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49818 q ha hb
    | true =>
      simp only [d125737, d171070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125738 q = 1) (hb : d171071 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, d171071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, d171071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125739 q = 1) (hb : d171072 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, d171072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, d171072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125740 q = 1) (hb : d171073 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, d171073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, d171073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125741 q = 1) (hb : d171074 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, d171074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, d171074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125742 q = 1) (hb : d171075 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, d171075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, d171075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49820 (p : Pattern) (ha : d20899 p = 1) (hb : d146837 p = 1) : d148553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d146837 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20897 q = 1) (hb : d146837 q = 1) : d148551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20897, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d146837 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20898 q = 1) (hb : d146837 q = 1) : d148552 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20898, d148552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20898, d148552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20899 q = 1) (hb : d146837 q = 1) : d148553 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20899, d148553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20899, d148553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro49821 (p : Pattern) (ha : d20905 p = 1) (hb : d146837 p = 1) : d148559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d146837 q = 1) : d148557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d146837 q = 1) : d148558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20905 q = 1) (hb : d146837 q = 1) : d148559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20905, d148559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20905, d148559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49822 (p : Pattern) (ha : d146837 p = 1) (hb : d150001 p = 1) : d148565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d146837 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d146837 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20906 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49821 q ha hb
    | true =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d149997 q = 1) : d148561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d149997, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d146837 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d149998 q = 1) : d148562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d149999 q = 1) : d148563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d149999, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150000 q = 1) : d148564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150000, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150001 q = 1) : d148565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150001, d148565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150001, d148565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49823 (p : Pattern) (ha : d20912 p = 1) (hb : d146837 p = 1) : d148566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d146837 q = 1) : d148557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d146837 q = 1) : d148558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20912 q = 1) (hb : d146837 q = 1) : d148566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20912, d148566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20912, d148566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49824 (p : Pattern) (ha : d146837 p = 1) (hb : d150006 p = 1) : d148572 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d146837 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d146837 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20906 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49821 q ha hb
    | true =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d149997 q = 1) : d148561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d149997, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d146837 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d149998 q = 1) : d148562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d149999 q = 1) : d148563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d149999, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150000 q = 1) : d148564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150000, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d146837 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d146837 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d146837 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20913 q = 1) (hb : d146837 q = 1) : d148567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49823 q ha hb
    | true =>
      simp only [d20913, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150002 q = 1) : d148568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d150002, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d146837 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150003 q = 1) : d148569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150003, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150004 q = 1) : d148570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150004, d148570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150004, d148570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146837 q = 1) (hb : d150005 q = 1) : d148571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150005, d148571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150005, d148571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d146837 q = 1) (hb : d150006 q = 1) : d148572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150006, d148572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150006, d148572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49825 (p : Pattern) (ha : d146837 p = 1) (hb : d150013 p = 1) : d148579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d146837 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d146837 q = 1) : d148567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49823 q ha hb
    | true =>
      simp only [d20913, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150002 q = 1) : d148568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150002, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d146837 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150003 q = 1) : d148569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150003, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150011 q = 1) : d148577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150011, d148577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150011, d148577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150012 q = 1) : d148578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150012, d148578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150012, d148578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150013 q = 1) : d148579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150013, d148579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150013, d148579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49826 (p : Pattern) (ha : d20938 p = 1) (hb : d146837 p = 1) : d148591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d146837 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20936 q = 1) (hb : d146837 q = 1) : d148589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20936, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d146837 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20937 q = 1) (hb : d146837 q = 1) : d148590 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20937, d148590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20937, d148590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20938 q = 1) (hb : d146837 q = 1) : d148591 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20938, d148591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20938, d148591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro49827 (p : Pattern) (ha : d20944 p = 1) (hb : d146837 p = 1) : d148597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d146837 q = 1) : d148592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49826 q ha hb
    | true =>
      simp only [d20939, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d146837 q = 1) : d148593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d146837 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20941 q = 1) (hb : d146837 q = 1) : d148594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20941, d148594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20941, d148594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20942 q = 1) (hb : d146837 q = 1) : d148595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20942, d148595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20942, d148595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20943 q = 1) (hb : d146837 q = 1) : d148596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20943, d148596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20943, d148596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20944 q = 1) (hb : d146837 q = 1) : d148597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20944, d148597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20944, d148597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49828 (p : Pattern) (ha : d146837 p = 1) (hb : d150023 p = 1) : d148603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d146837 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d146837 q = 1) : d148598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49827 q ha hb
    | true =>
      simp only [d20945, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150019 q = 1) : d148599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150019, d148599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150019, d148599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d146837 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150020 q = 1) : d148600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150020, d148600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150020, d148600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150021 q = 1) : d148601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150021, d148601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150021, d148601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150022 q = 1) : d148602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150022, d148602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150022, d148602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150023 q = 1) : d148603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150023, d148603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150023, d148603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49829 (p : Pattern) (ha : d146837 p = 1) (hb : d150029 p = 1) : d148609 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d146837 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150007 q = 1) : d148573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150007, d148573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49822 q ha hb
    | true =>
      simp only [d150007, d148573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49824 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d146837 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150008 q = 1) : d148574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150008, d148574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150008, d148574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150009 q = 1) : d148575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150009, d148575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150009, d148575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150010 q = 1) : d148576 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150010, d148576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150010, d148576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150014 q = 1) : d148580 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150014, d148580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150014, d148580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49825 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150015 q = 1) : d148581 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150015, d148581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150015, d148581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150016 q = 1) : d148582 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150016, d148582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150016, d148582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150017 q = 1) : d148583 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150017, d148583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150017, d148583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150018 q = 1) : d148584 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150018, d148584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150018, d148584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150024 q = 1) : d148604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150024, d148604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150024, d148604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49828 q ha hb
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150025 q = 1) : d148605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150025, d148605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150025, d148605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150026 q = 1) : d148606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150026, d148606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150026, d148606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150027 q = 1) : d148607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150027, d148607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150027, d148607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150028 q = 1) : d148608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150028, d148608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150028, d148608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150029 q = 1) : d148609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150029, d148609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150029, d148609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro49830 (p : Pattern) (ha : d20966 p = 1) (hb : d146837 p = 1) : d148619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49821 q ha hb
    | true =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d146837 q = 1) : d148615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d146837 q = 1) : d148616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d146837 q = 1) : d148617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d146837 q = 1) : d148618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20966 q = 1) (hb : d146837 q = 1) : d148619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49831 (p : Pattern) (ha : d20973 p = 1) (hb : d146837 p = 1) : d148626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49821 q ha hb
    | true =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d146837 q = 1) : d148615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d146837 q = 1) : d148616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d146837 q = 1) : d148617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d146837 q = 1) : d148618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d146837 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20913 q = 1) (hb : d146837 q = 1) : d148567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49823 q ha hb
    | true =>
      simp only [d20913, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20969 q = 1) (hb : d146837 q = 1) : d148622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20970 q = 1) (hb : d146837 q = 1) : d148623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20970, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20971 q = 1) (hb : d146837 q = 1) : d148624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20972 q = 1) (hb : d146837 q = 1) : d148625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20973 q = 1) (hb : d146837 q = 1) : d148626 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20973, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro49832 (p : Pattern) (ha : d21058 p = 1) (hb : d146837 p = 1) : d148687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49821 q ha hb
    | true =>
      simp only [d20906, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d146837 q = 1) : d148615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d146837 q = 1) : d148616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d146837 q = 1) : d148617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d146837 q = 1) : d148618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d146837 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21058 q = 1) (hb : d146837 q = 1) : d148687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21058, d148687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21058, d148687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49833 (p : Pattern) (ha : d20978 p = 1) (hb : d146837 p = 1) : d148631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d146837 q = 1) : d148557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d146837 q = 1) : d148630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20978 q = 1) (hb : d146837 q = 1) : d148631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20978, d148631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20978, d148631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49834 (p : Pattern) (ha : d20985 p = 1) (hb : d146837 p = 1) : d148638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d146837 q = 1) : d148636 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d146837 q = 1) : d148637 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20985 q = 1) (hb : d146837 q = 1) : d148638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20985, d148638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20985, d148638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49835 (p : Pattern) (ha : d21002 p = 1) (hb : d146837 p = 1) : d148648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20997 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
    | true =>
      simp only [d20997, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d20998 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20999 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20894 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20895 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20896 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21000 q = 1) (hb : d146837 q = 1) : d148646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21000, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d146837 q = 1) : d33 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20897 q = 1) (hb : d146837 q = 1) : d148551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20897, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21001 q = 1) (hb : d146837 q = 1) : d148647 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21001, d148647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21001, d148647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21002 q = 1) (hb : d146837 q = 1) : d148648 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21002, d148648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21002, d148648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro49836 (p : Pattern) (ha : d21008 p = 1) (hb : d146837 p = 1) : d148654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d146837 q = 1) : d148649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49835 q ha hb
    | true =>
      simp only [d21003, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d146837 q = 1) : d148650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d146837 q = 1) : d148651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d146837 q = 1) : d148652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d146837 q = 1) : d148653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21008 q = 1) (hb : d146837 q = 1) : d148654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21008, d148654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21008, d148654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49837 (p : Pattern) (ha : d21029 p = 1) (hb : d146837 p = 1) : d148660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d146837 q = 1) : d148657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d146837 q = 1) : d148658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d146837 q = 1) : d148659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21029 q = 1) (hb : d146837 q = 1) : d148660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21029, d148660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21029, d148660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49838 (p : Pattern) (ha : d146837 p = 1) (hb : d150039 p = 1) : d148666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d146837 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d146837 q = 1) : d148632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49833 q ha hb
    | true =>
      simp only [d20979, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d146837 q = 1) : d148633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d146837 q = 1) : d148634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d146837 q = 1) : d148635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d146837 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d146837 q = 1) : d148639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49834 q ha hb
    | true =>
      simp only [d20986, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d146837 q = 1) : d148640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d146837 q = 1) : d148641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d146837 q = 1) : d148655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49836 q ha hb
    | true =>
      simp only [d21009, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49821 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150035 q = 1) : d148656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150035, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d146837 q = 1) : d148661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49837 q ha hb
    | true =>
      simp only [d21030, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d146837 q = 1) : d148662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150036 q = 1) : d148663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150037 q = 1) : d148664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150037, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150038 q = 1) : d148665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150038, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150039 q = 1) : d148666 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d148666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150039, d148666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro49839 (p : Pattern) (ha : d21036 p = 1) (hb : d146837 p = 1) : d148667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d146837 q = 1) : d148557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d146837 q = 1) : d148630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21036 q = 1) (hb : d146837 q = 1) : d148667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21036, d148667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21036, d148667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49840 (p : Pattern) (ha : d21041 p = 1) (hb : d146837 p = 1) : d148672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d146837 q = 1) : d148636 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d146837 q = 1) : d148637 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21041 q = 1) (hb : d146837 q = 1) : d148672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21041, d148672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21041, d148672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49841 (p : Pattern) (ha : d21045 p = 1) (hb : d146837 p = 1) : d148676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d146837 q = 1) : d148649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49835 q ha hb
    | true =>
      simp only [d21003, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d146837 q = 1) : d148650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d146837 q = 1) : d148651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d146837 q = 1) : d148652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d146837 q = 1) : d148653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21045 q = 1) (hb : d146837 q = 1) : d148676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21045, d148676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21045, d148676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49842 (p : Pattern) (ha : d21050 p = 1) (hb : d146837 p = 1) : d148679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49820 q ha hb
    | true =>
      simp only [d20900, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d146837 q = 1) : d148657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d146837 q = 1) : d148658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d146837 q = 1) : d148659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21050 q = 1) (hb : d146837 q = 1) : d148679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21050, d148679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21050, d148679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49843 (p : Pattern) (ha : d146837 p = 1) (hb : d150044 p = 1) : d148685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d146837 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d146837 q = 1) : d148632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49833 q ha hb
    | true =>
      simp only [d20979, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d146837 q = 1) : d148633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d146837 q = 1) : d148634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d146837 q = 1) : d148635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d146837 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d146837 q = 1) : d148639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49834 q ha hb
    | true =>
      simp only [d20986, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d146837 q = 1) : d148640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d146837 q = 1) : d148641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d146837 q = 1) : d148655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49836 q ha hb
    | true =>
      simp only [d21009, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49821 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150035 q = 1) : d148656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150035, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d146837 q = 1) : d148661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49837 q ha hb
    | true =>
      simp only [d21030, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d146837 q = 1) : d148662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150036 q = 1) : d148663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150037 q = 1) : d148664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150037, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150038 q = 1) : d148665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150038, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d146837 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d21037 q = 1) (hb : d146837 q = 1) : d148668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21037, d148668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49839 q ha hb
    | true =>
      simp only [d21037, d148668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21038 q = 1) (hb : d146837 q = 1) : d148669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21038, d148669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21038, d148669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21039 q = 1) (hb : d146837 q = 1) : d148670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21039, d148670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21039, d148670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d21040 q = 1) (hb : d146837 q = 1) : d148671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21040, d148671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21040, d148671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d146837 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d21042 q = 1) (hb : d146837 q = 1) : d148673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21042, d148673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49840 q ha hb
    | true =>
      simp only [d21042, d148673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d21043 q = 1) (hb : d146837 q = 1) : d148674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21043, d148674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21043, d148674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d21044 q = 1) (hb : d146837 q = 1) : d148675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21044, d148675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21044, d148675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21046 q = 1) (hb : d146837 q = 1) : d148677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49841 q ha hb
    | true =>
      simp only [d21046, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49823 q ha hb
  have h27 (q : Pattern) (ha : d146837 q = 1) (hb : d150040 q = 1) : d148678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d150040, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d21051 q = 1) (hb : d146837 q = 1) : d148680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49842 q ha hb
    | true =>
      simp only [d21051, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d21052 q = 1) (hb : d146837 q = 1) : d148681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d21052, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d146837 q = 1) (hb : d150041 q = 1) : d148682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d150041, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d146837 q = 1) (hb : d150042 q = 1) : d148683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d148683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d150042, d148683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d146837 q = 1) (hb : d150043 q = 1) : d148684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d148684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150043, d148684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d146837 q = 1) (hb : d150044 q = 1) : d148685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d148685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150044, d148685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro49844 (p : Pattern) (ha : d146837 p = 1) (hb : d150051 p = 1) : d148694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21046 q = 1) (hb : d146837 q = 1) : d148677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49841 q ha hb
    | true =>
      simp only [d21046, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49823 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150040 q = 1) : d148678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150040, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21051 q = 1) (hb : d146837 q = 1) : d148680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49842 q ha hb
    | true =>
      simp only [d21051, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21052 q = 1) (hb : d146837 q = 1) : d148681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21052, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150041 q = 1) : d148682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150041, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150049 q = 1) : d148692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d148692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150049, d148692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150050 q = 1) : d148693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d148693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150050, d148693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150051 q = 1) : d148694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d148694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150051, d148694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49845 (p : Pattern) (ha : d21083 p = 1) (hb : d146837 p = 1) : d148706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20932 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21078 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
    | true =>
      simp only [d21078, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21079 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21080 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20933 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20934 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20935 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21081 q = 1) (hb : d146837 q = 1) : d148704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21081, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d146837 q = 1) : d74 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20936 q = 1) (hb : d146837 q = 1) : d148589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20936, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21082 q = 1) (hb : d146837 q = 1) : d148705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21082, d148705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21082, d148705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21083 q = 1) (hb : d146837 q = 1) : d148706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21083, d148706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21083, d148706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro49846 (p : Pattern) (ha : d21089 p = 1) (hb : d146837 p = 1) : d148712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21084 q = 1) (hb : d146837 q = 1) : d148707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21084, d148707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49845 q ha hb
    | true =>
      simp only [d21084, d148707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21085 q = 1) (hb : d146837 q = 1) : d148708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21085, d148708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21085, d148708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20939 q = 1) (hb : d146837 q = 1) : d148592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49826 q ha hb
    | true =>
      simp only [d20939, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20940 q = 1) (hb : d146837 q = 1) : d148593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21086 q = 1) (hb : d146837 q = 1) : d148709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21086, d148709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21086, d148709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21087 q = 1) (hb : d146837 q = 1) : d148710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21087, d148710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21087, d148710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21088 q = 1) (hb : d146837 q = 1) : d148711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21088, d148711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21088, d148711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21089 q = 1) (hb : d146837 q = 1) : d148712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21089, d148712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21089, d148712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49847 (p : Pattern) (ha : d21110 p = 1) (hb : d146837 p = 1) : d148718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d146837 q = 1) : d148592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49826 q ha hb
    | true =>
      simp only [d20939, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d146837 q = 1) : d148593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21107 q = 1) (hb : d146837 q = 1) : d148715 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21107, d148715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21107, d148715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21108 q = 1) (hb : d146837 q = 1) : d148716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21108, d148716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21108, d148716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21109 q = 1) (hb : d146837 q = 1) : d148717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21109, d148717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21109, d148717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21110 q = 1) (hb : d146837 q = 1) : d148718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21110, d148718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21110, d148718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49848 (p : Pattern) (ha : d146837 p = 1) (hb : d150061 p = 1) : d148724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21090 q = 1) (hb : d146837 q = 1) : d148713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21090, d148713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49846 q ha hb
    | true =>
      simp only [d21090, d148713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49827 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150057 q = 1) : d148714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d148714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150057, d148714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21111 q = 1) (hb : d146837 q = 1) : d148719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21111, d148719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49847 q ha hb
    | true =>
      simp only [d21111, d148719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21112 q = 1) (hb : d146837 q = 1) : d148720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21112, d148720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21112, d148720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150058 q = 1) : d148721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d148721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150058, d148721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150059 q = 1) : d148722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d148722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150059, d148722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150060 q = 1) : d148723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d148723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150060, d148723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150061 q = 1) : d148724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d148724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150061, d148724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49849 (p : Pattern) (ha : d146837 p = 1) (hb : d150067 p = 1) : d148730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20967 q = 1) (hb : d146837 q = 1) : d148620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20967, d148620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20967, d148620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49830 q ha hb
  have h2 (q : Pattern) (ha : d20968 q = 1) (hb : d146837 q = 1) : d148621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20968, d148621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20968, d148621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20974 q = 1) (hb : d146837 q = 1) : d148627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49830 q ha hb
    | true =>
      simp only [d20974, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49831 q ha hb
  have h4 (q : Pattern) (ha : d20975 q = 1) (hb : d146837 q = 1) : d148628 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20975, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20976 q = 1) (hb : d146837 q = 1) : d148629 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20976, d148629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20976, d148629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150045 q = 1) : d148686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d148686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49838 q ha hb
    | true =>
      simp only [d150045, d148686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49843 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d146837 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21059 q = 1) (hb : d146837 q = 1) : d148688 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21059, d148688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49832 q ha hb
    | true =>
      simp only [d21059, d148688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150046 q = 1) : d148689 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d148689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150046, d148689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150047 q = 1) : d148690 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d148690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150047, d148690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150048 q = 1) : d148691 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d148691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150048, d148691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150052 q = 1) : d148695 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d148695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150052, d148695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49844 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d146837 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150053 q = 1) : d148696 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d148696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150053, d148696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150054 q = 1) : d148697 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d148697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150054, d148697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150055 q = 1) : d148698 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d148698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150055, d148698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150056 q = 1) : d148699 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d148699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150056, d148699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146837 q = 1) (hb : d150062 q = 1) : d148725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d148725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150062, d148725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49848 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d146837 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d146837 q = 1) (hb : d150063 q = 1) : d148726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d148726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150063, d148726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d146837 q = 1) (hb : d150064 q = 1) : d148727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d148727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150064, d148727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146837 q = 1) (hb : d150065 q = 1) : d148728 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d148728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150065, d148728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150066 q = 1) : d148729 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d148729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150066, d148729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d146837 q = 1) (hb : d150067 q = 1) : d148730 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d148730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150067, d148730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro49850 (p : Pattern) (ha : d146837 p = 1) (hb : d150073 p = 1) : d148736 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d146837 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150030 q = 1) : d148610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150030, d148610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150030, d148610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49829 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150031 q = 1) : d148611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150031, d148611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150031, d148611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150032 q = 1) : d148612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150032, d148612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150032, d148612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150033 q = 1) : d148613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150033, d148613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150033, d148613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150034 q = 1) : d148614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150034, d148614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150034, d148614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150068 q = 1) : d148731 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d148731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150068, d148731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49849 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150069 q = 1) : d148732 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d148732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150069, d148732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150070 q = 1) : d148733 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d148733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150070, d148733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150071 q = 1) : d148734 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d148734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150071, d148734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150072 q = 1) : d148735 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d148735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150072, d148735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150073 q = 1) : d148736 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d148736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150073, d148736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro49851 (p : Pattern) (ha : d21131 p = 1) (hb : d146837 p = 1) : d148739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20997 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
    | true =>
      simp only [d20997, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d20998 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20999 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20894 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20895 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20896 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21000 q = 1) (hb : d146837 q = 1) : d148646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21000, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21129 q = 1) (hb : d146837 q = 1) : d148737 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21129, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21130 q = 1) (hb : d146837 q = 1) : d148738 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21130, d148738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21130, d148738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21131 q = 1) (hb : d146837 q = 1) : d148739 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21131, d148739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21131, d148739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49852 (p : Pattern) (ha : d21135 p = 1) (hb : d146837 p = 1) : d148743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21129 q = 1) (hb : d146837 q = 1) : d148737 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21129, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21134 q = 1) (hb : d146837 q = 1) : d148742 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21134, d148742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21134, d148742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21135 q = 1) (hb : d146837 q = 1) : d148743 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21135, d148743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21135, d148743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49853 (p : Pattern) (ha : d21141 p = 1) (hb : d146837 p = 1) : d148749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d146837 q = 1) : d148747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d146837 q = 1) : d148748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21141 q = 1) (hb : d146837 q = 1) : d148749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21141, d148749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21141, d148749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49854 (p : Pattern) (ha : d21145 p = 1) (hb : d146837 p = 1) : d148753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d146837 q = 1) : d148751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d146837 q = 1) : d148752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21145 q = 1) (hb : d146837 q = 1) : d148753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21145, d148753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21145, d148753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49855 (p : Pattern) (ha : d21151 p = 1) (hb : d146837 p = 1) : d148759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d146837 q = 1) : d148754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49853 q ha hb
    | true =>
      simp only [d21146, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49854 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d146837 q = 1) : d148755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d146837 q = 1) : d148756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d146837 q = 1) : d148757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d146837 q = 1) : d148758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21151 q = 1) (hb : d146837 q = 1) : d148759 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21151, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21151, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49856 (p : Pattern) (ha : d21154 p = 1) (hb : d146837 p = 1) : d148762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d146837 q = 1) : d148747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d146837 q = 1) : d148748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21154 q = 1) (hb : d146837 q = 1) : d148762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21154, d148762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21154, d148762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49857 (p : Pattern) (ha : d21155 p = 1) (hb : d146837 p = 1) : d148763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d146837 q = 1) : d148751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d146837 q = 1) : d148752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21155 q = 1) (hb : d146837 q = 1) : d148763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21155, d148763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21155, d148763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49858 (p : Pattern) (ha : d21161 p = 1) (hb : d146837 p = 1) : d148769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d146837 q = 1) : d148754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49853 q ha hb
    | true =>
      simp only [d21146, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49854 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d146837 q = 1) : d148755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d146837 q = 1) : d148756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d146837 q = 1) : d148757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d146837 q = 1) : d148758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21156 q = 1) (hb : d146837 q = 1) : d148764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49856 q ha hb
    | true =>
      simp only [d21156, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49857 q ha hb
  have h7 (q : Pattern) (ha : d21157 q = 1) (hb : d146837 q = 1) : d148765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21158 q = 1) (hb : d146837 q = 1) : d148766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21158, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21159 q = 1) (hb : d146837 q = 1) : d148767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21160 q = 1) (hb : d146837 q = 1) : d148768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21161 q = 1) (hb : d146837 q = 1) : d148769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21161, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21161, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49859 (p : Pattern) (ha : d21288 p = 1) (hb : d146837 p = 1) : d148842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d146837 q = 1) : d148754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49853 q ha hb
    | true =>
      simp only [d21146, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49854 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d146837 q = 1) : d148755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d146837 q = 1) : d148756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d146837 q = 1) : d148757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d146837 q = 1) : d148758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21283 q = 1) (hb : d146837 q = 1) : d148837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49854 q ha hb
    | true =>
      simp only [d21283, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21284 q = 1) (hb : d146837 q = 1) : d148838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21285 q = 1) (hb : d146837 q = 1) : d148839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21285, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21286 q = 1) (hb : d146837 q = 1) : d148840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21287 q = 1) (hb : d146837 q = 1) : d148841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21288 q = 1) (hb : d146837 q = 1) : d148842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21288, d148842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21288, d148842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49860 (p : Pattern) (ha : d21294 p = 1) (hb : d146837 p = 1) : d148848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21283 q = 1) (hb : d146837 q = 1) : d148837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49854 q ha hb
    | true =>
      simp only [d21283, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21284 q = 1) (hb : d146837 q = 1) : d148838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21285 q = 1) (hb : d146837 q = 1) : d148839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21285, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21286 q = 1) (hb : d146837 q = 1) : d148840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21287 q = 1) (hb : d146837 q = 1) : d148841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21289 q = 1) (hb : d146837 q = 1) : d148843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49857 q ha hb
    | true =>
      simp only [d21289, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21290 q = 1) (hb : d146837 q = 1) : d148844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21291 q = 1) (hb : d146837 q = 1) : d148845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21291, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21292 q = 1) (hb : d146837 q = 1) : d148846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21293 q = 1) (hb : d146837 q = 1) : d148847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21294 q = 1) (hb : d146837 q = 1) : d148848 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21294, d148848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21294, d148848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49861 (p : Pattern) (ha : d21303 p = 1) (hb : d146837 p = 1) : d148857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21289 q = 1) (hb : d146837 q = 1) : d148843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49857 q ha hb
    | true =>
      simp only [d21289, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21290 q = 1) (hb : d146837 q = 1) : d148844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21291 q = 1) (hb : d146837 q = 1) : d148845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21291, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21292 q = 1) (hb : d146837 q = 1) : d148846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21293 q = 1) (hb : d146837 q = 1) : d148847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21303 q = 1) (hb : d146837 q = 1) : d148857 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21303, d148857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21303, d148857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49862 (p : Pattern) (ha : d21342 p = 1) (hb : d146837 p = 1) : d148882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21332 q = 1) (hb : d146837 q = 1) : d148872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21332, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21341 q = 1) (hb : d146837 q = 1) : d148881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21341, d148881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21341, d148881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21342 q = 1) (hb : d146837 q = 1) : d148882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21342, d148882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21342, d148882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49863 (p : Pattern) (ha : d21398 p = 1) (hb : d146837 p = 1) : d148905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21343 q = 1) (hb : d146837 q = 1) : d148883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49862 q ha hb
    | true =>
      simp only [d21343, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21344 q = 1) (hb : d146837 q = 1) : d148884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21395 q = 1) (hb : d146837 q = 1) : d148902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21395, d148902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21395, d148902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21396 q = 1) (hb : d146837 q = 1) : d148903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21396, d148903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21396, d148903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21397 q = 1) (hb : d146837 q = 1) : d148904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21397, d148904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21397, d148904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21398 q = 1) (hb : d146837 q = 1) : d148905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21398, d148905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21398, d148905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49864 (p : Pattern) (ha : d21404 p = 1) (hb : d146837 p = 1) : d148911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21399 q = 1) (hb : d146837 q = 1) : d148906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21399, d148906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49863 q ha hb
    | true =>
      simp only [d21399, d148906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21400 q = 1) (hb : d146837 q = 1) : d148907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21400, d148907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21400, d148907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21401 q = 1) (hb : d146837 q = 1) : d148908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21401, d148908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21401, d148908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21402 q = 1) (hb : d146837 q = 1) : d148909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21402, d148909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21402, d148909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21403 q = 1) (hb : d146837 q = 1) : d148910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21403, d148910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21403, d148910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21404 q = 1) (hb : d146837 q = 1) : d148911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21404, d148911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21404, d148911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49865 (p : Pattern) (ha : d21166 p = 1) (hb : d146837 p = 1) : d148774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d146837 q = 1) : d148747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d146837 q = 1) : d148773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21166 q = 1) (hb : d146837 q = 1) : d148774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21166, d148774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21166, d148774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49866 (p : Pattern) (ha : d21168 p = 1) (hb : d146837 p = 1) : d148776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d146837 q = 1) : d148751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d146837 q = 1) : d148775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21168 q = 1) (hb : d146837 q = 1) : d148776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21168, d148776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21168, d148776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49867 (p : Pattern) (ha : d21175 p = 1) (hb : d146837 p = 1) : d148783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d146837 q = 1) : d148781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d146837 q = 1) : d148782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21175 q = 1) (hb : d146837 q = 1) : d148783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21175, d148783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21175, d148783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49868 (p : Pattern) (ha : d21178 p = 1) (hb : d146837 p = 1) : d148786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d146837 q = 1) : d148784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d146837 q = 1) : d148785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21178 q = 1) (hb : d146837 q = 1) : d148786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21178, d148786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21178, d148786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49869 (p : Pattern) (ha : d21204 p = 1) (hb : d146837 p = 1) : d148796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21195 q = 1) (hb : d146837 q = 1) : d148791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21195, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45777 q ha hb
    | true =>
      simp only [d21195, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21196 q = 1) (hb : d146837 q = 1) : d148792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21196, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21196, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21197 q = 1) (hb : d146837 q = 1) : d148793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21197, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21197, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21198 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21199 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21199, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
    | true =>
      simp only [d21199, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21200 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21200, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21200, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21201 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21201, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21201, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21202 q = 1) (hb : d146837 q = 1) : d148794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21202, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21202, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d20893 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20997 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45741 q ha hb
    | true =>
      simp only [d20997, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d20998 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20999 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20894 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45724 q ha hb
    | true =>
      simp only [d20894, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d20895 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20896 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21000 q = 1) (hb : d146837 q = 1) : d148646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21000, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21203 q = 1) (hb : d146837 q = 1) : d148795 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21203, d148795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21203, d148795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21204 q = 1) (hb : d146837 q = 1) : d148796 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21204, d148796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21204, d148796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro49870 (p : Pattern) (ha : d21210 p = 1) (hb : d146837 p = 1) : d148802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d146837 q = 1) : d148797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49869 q ha hb
    | true =>
      simp only [d21205, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d146837 q = 1) : d148798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d146837 q = 1) : d148799 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d146837 q = 1) : d148800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d146837 q = 1) : d148801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21210 q = 1) (hb : d146837 q = 1) : d148802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21210, d148802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21210, d148802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49871 (p : Pattern) (ha : d21251 p = 1) (hb : d146837 p = 1) : d148808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d146837 q = 1) : d148805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d146837 q = 1) : d148806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d146837 q = 1) : d148807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21251 q = 1) (hb : d146837 q = 1) : d148808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21251, d148808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21251, d148808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49872 (p : Pattern) (ha : d146837 p = 1) (hb : d150078 p = 1) : d148814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d146837 q = 1) : d148777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49865 q ha hb
    | true =>
      simp only [d21169, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49866 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d146837 q = 1) : d148778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d146837 q = 1) : d148779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d146837 q = 1) : d148780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d146837 q = 1) : d148787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49867 q ha hb
    | true =>
      simp only [d21179, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49868 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d146837 q = 1) : d148788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d146837 q = 1) : d148789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d146837 q = 1) : d148803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49870 q ha hb
    | true =>
      simp only [d21211, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49853 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150074 q = 1) : d148804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150074, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d146837 q = 1) : d148809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49871 q ha hb
    | true =>
      simp only [d21252, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d146837 q = 1) : d148810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150075 q = 1) : d148811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150076 q = 1) : d148812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150076, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150077 q = 1) : d148813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150077, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150078 q = 1) : d148814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d148814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150078, d148814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49873 (p : Pattern) (ha : d21258 p = 1) (hb : d146837 p = 1) : d148815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d146837 q = 1) : d148747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d146837 q = 1) : d148773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21258 q = 1) (hb : d146837 q = 1) : d148815 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21258, d148815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21258, d148815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49874 (p : Pattern) (ha : d21259 p = 1) (hb : d146837 p = 1) : d148816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d146837 q = 1) : d148751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d146837 q = 1) : d148775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21259 q = 1) (hb : d146837 q = 1) : d148816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21259, d148816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21259, d148816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49875 (p : Pattern) (ha : d21264 p = 1) (hb : d146837 p = 1) : d148821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d146837 q = 1) : d148781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d146837 q = 1) : d148782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21264 q = 1) (hb : d146837 q = 1) : d148821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21264, d148821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21264, d148821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49876 (p : Pattern) (ha : d21265 p = 1) (hb : d146837 p = 1) : d148822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49852 q ha hb
    | true =>
      simp only [d21136, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d146837 q = 1) : d148784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d146837 q = 1) : d148785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21265 q = 1) (hb : d146837 q = 1) : d148822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21265, d148822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21265, d148822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49877 (p : Pattern) (ha : d21269 p = 1) (hb : d146837 p = 1) : d148826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d146837 q = 1) : d148797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49869 q ha hb
    | true =>
      simp only [d21205, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d146837 q = 1) : d148798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d146837 q = 1) : d148799 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d146837 q = 1) : d148800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d146837 q = 1) : d148801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21269 q = 1) (hb : d146837 q = 1) : d148826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21269, d148826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21269, d148826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49878 (p : Pattern) (ha : d21275 p = 1) (hb : d146837 p = 1) : d148829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49851 q ha hb
    | true =>
      simp only [d21132, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d146837 q = 1) : d148805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d146837 q = 1) : d148806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d146837 q = 1) : d148807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21275 q = 1) (hb : d146837 q = 1) : d148829 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21275, d148829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21275, d148829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49879 (p : Pattern) (ha : d146837 p = 1) (hb : d150083 p = 1) : d148835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d146837 q = 1) : d148777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49865 q ha hb
    | true =>
      simp only [d21169, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49866 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d146837 q = 1) : d148778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d146837 q = 1) : d148779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d146837 q = 1) : d148780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d146837 q = 1) : d148787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49867 q ha hb
    | true =>
      simp only [d21179, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49868 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d146837 q = 1) : d148788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d146837 q = 1) : d148789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d146837 q = 1) : d148803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49870 q ha hb
    | true =>
      simp only [d21211, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49853 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150074 q = 1) : d148804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150074, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d146837 q = 1) : d148809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49871 q ha hb
    | true =>
      simp only [d21252, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d146837 q = 1) : d148810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150075 q = 1) : d148811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150076 q = 1) : d148812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150076, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150077 q = 1) : d148813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150077, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21260 q = 1) (hb : d146837 q = 1) : d148817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21260, d148817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49873 q ha hb
    | true =>
      simp only [d21260, d148817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49874 q ha hb
  have h16 (q : Pattern) (ha : d21261 q = 1) (hb : d146837 q = 1) : d148818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21261, d148818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21261, d148818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21262 q = 1) (hb : d146837 q = 1) : d148819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21262, d148819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21262, d148819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21263 q = 1) (hb : d146837 q = 1) : d148820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21263, d148820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21263, d148820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21266 q = 1) (hb : d146837 q = 1) : d148823 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21266, d148823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49875 q ha hb
    | true =>
      simp only [d21266, d148823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49876 q ha hb
  have h20 (q : Pattern) (ha : d21267 q = 1) (hb : d146837 q = 1) : d148824 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21267, d148824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21267, d148824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21268 q = 1) (hb : d146837 q = 1) : d148825 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21268, d148825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21268, d148825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21270 q = 1) (hb : d146837 q = 1) : d148827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49877 q ha hb
    | true =>
      simp only [d21270, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49856 q ha hb
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150079 q = 1) : d148828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150079, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21276 q = 1) (hb : d146837 q = 1) : d148830 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49878 q ha hb
    | true =>
      simp only [d21276, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21277 q = 1) (hb : d146837 q = 1) : d148831 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21277, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146837 q = 1) (hb : d150080 q = 1) : d148832 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150080, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146837 q = 1) (hb : d150081 q = 1) : d148833 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d148833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150081, d148833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146837 q = 1) (hb : d150082 q = 1) : d148834 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d148834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150082, d148834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146837 q = 1) (hb : d150083 q = 1) : d148835 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d148835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150083, d148835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro49880 (p : Pattern) (ha : d146837 p = 1) (hb : d150090 p = 1) : d148855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21270 q = 1) (hb : d146837 q = 1) : d148827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49877 q ha hb
    | true =>
      simp only [d21270, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49856 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150079 q = 1) : d148828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150079, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21276 q = 1) (hb : d146837 q = 1) : d148830 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49878 q ha hb
    | true =>
      simp only [d21276, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21277 q = 1) (hb : d146837 q = 1) : d148831 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21277, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150080 q = 1) : d148832 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150080, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150088 q = 1) : d148853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d148853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150088, d148853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150089 q = 1) : d148854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d148854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150089, d148854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150090 q = 1) : d148855 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d148855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150090, d148855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49881 (p : Pattern) (ha : d21329 p = 1) (hb : d146837 p = 1) : d148869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21077 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21320 q = 1) (hb : d146837 q = 1) : d148864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21320, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45791 q ha hb
    | true =>
      simp only [d21320, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21321 q = 1) (hb : d146837 q = 1) : d148865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21321, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21321, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21322 q = 1) (hb : d146837 q = 1) : d148866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21322, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21322, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21323 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21324 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21324, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
    | true =>
      simp only [d21324, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21325 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21325, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21325, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21326 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21326, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21326, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21327 q = 1) (hb : d146837 q = 1) : d148867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21327, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21327, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d20932 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d21078 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
    | true =>
      simp only [d21078, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d21079 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21080 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20933 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d20934 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20935 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21081 q = 1) (hb : d146837 q = 1) : d148704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21081, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21328 q = 1) (hb : d146837 q = 1) : d148868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21328, d148868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21328, d148868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21329 q = 1) (hb : d146837 q = 1) : d148869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21329, d148869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21329, d148869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro49882 (p : Pattern) (ha : d21334 p = 1) (hb : d146837 p = 1) : d148874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20932 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21078 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45752 q ha hb
    | true =>
      simp only [d21078, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21079 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21080 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d71 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20933 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45731 q ha hb
    | true =>
      simp only [d20933, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d20934 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20935 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21081 q = 1) (hb : d146837 q = 1) : d148704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21081, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21332 q = 1) (hb : d146837 q = 1) : d148872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21332, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21333 q = 1) (hb : d146837 q = 1) : d148873 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21333, d148873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21333, d148873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21334 q = 1) (hb : d146837 q = 1) : d148874 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21334, d148874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21334, d148874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49883 (p : Pattern) (ha : d21340 p = 1) (hb : d146837 p = 1) : d148880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21330 q = 1) (hb : d146837 q = 1) : d148870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21330, d148870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49881 q ha hb
    | true =>
      simp only [d21330, d148870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21331 q = 1) (hb : d146837 q = 1) : d148871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21331, d148871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21331, d148871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21335 q = 1) (hb : d146837 q = 1) : d148875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49882 q ha hb
    | true =>
      simp only [d21335, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21336 q = 1) (hb : d146837 q = 1) : d148876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21337 q = 1) (hb : d146837 q = 1) : d148877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21337, d148877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21337, d148877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21338 q = 1) (hb : d146837 q = 1) : d148878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21338, d148878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21338, d148878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21339 q = 1) (hb : d146837 q = 1) : d148879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21339, d148879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21339, d148879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21340 q = 1) (hb : d146837 q = 1) : d148880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21340, d148880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21340, d148880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49884 (p : Pattern) (ha : d21348 p = 1) (hb : d146837 p = 1) : d148888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d146837 q = 1) : d148875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49882 q ha hb
    | true =>
      simp only [d21335, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d146837 q = 1) : d148876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21343 q = 1) (hb : d146837 q = 1) : d148883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49862 q ha hb
    | true =>
      simp only [d21343, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21344 q = 1) (hb : d146837 q = 1) : d148884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21345 q = 1) (hb : d146837 q = 1) : d148885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21345, d148885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21345, d148885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21346 q = 1) (hb : d146837 q = 1) : d148886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21346, d148886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21346, d148886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21347 q = 1) (hb : d146837 q = 1) : d148887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21347, d148887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21347, d148887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21348 q = 1) (hb : d146837 q = 1) : d148888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21348, d148888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21348, d148888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49885 (p : Pattern) (ha : d21387 p = 1) (hb : d146837 p = 1) : d148894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d146837 q = 1) : d148875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49882 q ha hb
    | true =>
      simp only [d21335, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d146837 q = 1) : d148876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21384 q = 1) (hb : d146837 q = 1) : d148891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21384, d148891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21384, d148891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21385 q = 1) (hb : d146837 q = 1) : d148892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21385, d148892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21385, d148892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21386 q = 1) (hb : d146837 q = 1) : d148893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21386, d148893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21386, d148893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21387 q = 1) (hb : d146837 q = 1) : d148894 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21387, d148894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21387, d148894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49886 (p : Pattern) (ha : d146837 p = 1) (hb : d150100 p = 1) : d148900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21349 q = 1) (hb : d146837 q = 1) : d148889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21349, d148889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49883 q ha hb
    | true =>
      simp only [d21349, d148889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49884 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150096 q = 1) : d148890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d148890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150096, d148890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21388 q = 1) (hb : d146837 q = 1) : d148895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21388, d148895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49885 q ha hb
    | true =>
      simp only [d21388, d148895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21389 q = 1) (hb : d146837 q = 1) : d148896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21389, d148896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21389, d148896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150097 q = 1) : d148897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d148897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150097, d148897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150098 q = 1) : d148898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d148898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150098, d148898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150099 q = 1) : d148899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d148899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150099, d148899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150100 q = 1) : d148900 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d148900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150100, d148900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49887 (p : Pattern) (ha : d146837 p = 1) (hb : d150106 p = 1) : d148917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21152 q = 1) (hb : d146837 q = 1) : d148760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21152, d148760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21152, d148760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49855 q ha hb
  have h2 (q : Pattern) (ha : d21153 q = 1) (hb : d146837 q = 1) : d148761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21153, d148761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21153, d148761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21162 q = 1) (hb : d146837 q = 1) : d148770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49855 q ha hb
    | true =>
      simp only [d21162, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49858 q ha hb
  have h4 (q : Pattern) (ha : d21163 q = 1) (hb : d146837 q = 1) : d148771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21163, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21164 q = 1) (hb : d146837 q = 1) : d148772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21164, d148772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21164, d148772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150084 q = 1) : d148836 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d148836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49872 q ha hb
    | true =>
      simp only [d150084, d148836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49879 q ha hb
  have h7 (q : Pattern) (ha : d21295 q = 1) (hb : d146837 q = 1) : d148849 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21295, d148849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49859 q ha hb
    | true =>
      simp only [d21295, d148849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49860 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150085 q = 1) : d148850 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d148850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150085, d148850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150086 q = 1) : d148851 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d148851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150086, d148851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150087 q = 1) : d148852 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d148852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150087, d148852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150091 q = 1) : d148856 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d148856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150091, d148856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49880 q ha hb
  have h12 (q : Pattern) (ha : d21304 q = 1) (hb : d146837 q = 1) : d148858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21304, d148858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21304, d148858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49861 q ha hb
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150092 q = 1) : d148859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d148859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150092, d148859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150093 q = 1) : d148860 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d148860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150093, d148860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150094 q = 1) : d148861 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d148861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150094, d148861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150095 q = 1) : d148862 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d148862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150095, d148862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150101 q = 1) : d148901 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d148901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150101, d148901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49886 q ha hb
  have h18 (q : Pattern) (ha : d21405 q = 1) (hb : d146837 q = 1) : d148912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21405, d148912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21405, d148912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49864 q ha hb
  have h19 (q : Pattern) (ha : d146837 q = 1) (hb : d150102 q = 1) : d148913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d148913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150102, d148913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146837 q = 1) (hb : d150103 q = 1) : d148914 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d148914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150103, d148914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146837 q = 1) (hb : d150104 q = 1) : d148915 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d148915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150104, d148915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146837 q = 1) (hb : d150105 q = 1) : d148916 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d148916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150105, d148916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150106 q = 1) : d148917 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d148917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150106, d148917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49888 (p : Pattern) (ha : d146837 p = 1) (hb : d150112 p = 1) : d148923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150107 q = 1) : d148918 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d148918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150107, d148918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49887 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150108 q = 1) : d148919 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d148919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150108, d148919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150109 q = 1) : d148920 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d148920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150109, d148920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150110 q = 1) : d148921 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d148921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150110, d148921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150111 q = 1) : d148922 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d148922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150111, d148922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150112 q = 1) : d148923 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d148923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150112, d148923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49889 (p : Pattern) (ha : d21430 p = 1) (hb : d146837 p = 1) : d148927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21421 q = 1) (hb : d146837 q = 1) : d148791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45801 q ha hb
    | true =>
      simp only [d21421, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21422 q = 1) (hb : d146837 q = 1) : d148792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21423 q = 1) (hb : d146837 q = 1) : d148793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21424 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45802 q ha hb
    | true =>
      simp only [d21424, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21425 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21426 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21427 q = 1) (hb : d146837 q = 1) : d148794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21427, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21428 q = 1) (hb : d146837 q = 1) : d148925 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21428, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21429 q = 1) (hb : d146837 q = 1) : d148926 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21429, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21429, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21430 q = 1) (hb : d146837 q = 1) : d148927 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21430, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21430, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49890 (p : Pattern) (ha : d21434 p = 1) (hb : d146837 p = 1) : d148931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21424 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45802 q ha hb
    | true =>
      simp only [d21424, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21425 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21426 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21428 q = 1) (hb : d146837 q = 1) : d148925 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21428, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21433 q = 1) (hb : d146837 q = 1) : d148930 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21433, d148930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21433, d148930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21434 q = 1) (hb : d146837 q = 1) : d148931 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21434, d148931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21434, d148931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49891 (p : Pattern) (ha : d21440 p = 1) (hb : d146837 p = 1) : d148937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d146837 q = 1) : d148935 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d146837 q = 1) : d148936 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21440 q = 1) (hb : d146837 q = 1) : d148937 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21440, d148937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21440, d148937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49892 (p : Pattern) (ha : d21444 p = 1) (hb : d146837 p = 1) : d148941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d146837 q = 1) : d148939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d146837 q = 1) : d148940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21444 q = 1) (hb : d146837 q = 1) : d148941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21444, d148941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21444, d148941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49893 (p : Pattern) (ha : d21450 p = 1) (hb : d146837 p = 1) : d148947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d146837 q = 1) : d148942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49891 q ha hb
    | true =>
      simp only [d21445, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49892 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d146837 q = 1) : d148943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d146837 q = 1) : d148944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d146837 q = 1) : d148945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d146837 q = 1) : d148946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21450 q = 1) (hb : d146837 q = 1) : d148947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49894 (p : Pattern) (ha : d21453 p = 1) (hb : d146837 p = 1) : d148950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d146837 q = 1) : d148935 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d146837 q = 1) : d148936 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21453 q = 1) (hb : d146837 q = 1) : d148950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21453, d148950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21453, d148950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49895 (p : Pattern) (ha : d21454 p = 1) (hb : d146837 p = 1) : d148951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d146837 q = 1) : d148939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d146837 q = 1) : d148940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21454 q = 1) (hb : d146837 q = 1) : d148951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21454, d148951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21454, d148951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49896 (p : Pattern) (ha : d21460 p = 1) (hb : d146837 p = 1) : d148957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d146837 q = 1) : d148942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49891 q ha hb
    | true =>
      simp only [d21445, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49892 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d146837 q = 1) : d148943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d146837 q = 1) : d148944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d146837 q = 1) : d148945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d146837 q = 1) : d148946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21455 q = 1) (hb : d146837 q = 1) : d148952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49894 q ha hb
    | true =>
      simp only [d21455, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49895 q ha hb
  have h7 (q : Pattern) (ha : d21456 q = 1) (hb : d146837 q = 1) : d148953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21457 q = 1) (hb : d146837 q = 1) : d148954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21457, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21458 q = 1) (hb : d146837 q = 1) : d148955 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21459 q = 1) (hb : d146837 q = 1) : d148956 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21460 q = 1) (hb : d146837 q = 1) : d148957 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21460, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49897 (p : Pattern) (ha : d21591 p = 1) (hb : d146837 p = 1) : d149030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d146837 q = 1) : d148942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49891 q ha hb
    | true =>
      simp only [d21445, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49892 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d146837 q = 1) : d148943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d146837 q = 1) : d148944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d146837 q = 1) : d148945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d146837 q = 1) : d148946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21586 q = 1) (hb : d146837 q = 1) : d149025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49892 q ha hb
    | true =>
      simp only [d21586, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21587 q = 1) (hb : d146837 q = 1) : d149026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21588 q = 1) (hb : d146837 q = 1) : d149027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21588, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21589 q = 1) (hb : d146837 q = 1) : d149028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21590 q = 1) (hb : d146837 q = 1) : d149029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21591 q = 1) (hb : d146837 q = 1) : d149030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21591, d149030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21591, d149030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49898 (p : Pattern) (ha : d21597 p = 1) (hb : d146837 p = 1) : d149036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21586 q = 1) (hb : d146837 q = 1) : d149025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49892 q ha hb
    | true =>
      simp only [d21586, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21587 q = 1) (hb : d146837 q = 1) : d149026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21588 q = 1) (hb : d146837 q = 1) : d149027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21588, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21589 q = 1) (hb : d146837 q = 1) : d149028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21590 q = 1) (hb : d146837 q = 1) : d149029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21592 q = 1) (hb : d146837 q = 1) : d149031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49895 q ha hb
    | true =>
      simp only [d21592, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21593 q = 1) (hb : d146837 q = 1) : d149032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21594 q = 1) (hb : d146837 q = 1) : d149033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21594, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21595 q = 1) (hb : d146837 q = 1) : d149034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21596 q = 1) (hb : d146837 q = 1) : d149035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21597 q = 1) (hb : d146837 q = 1) : d149036 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21597, d149036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21597, d149036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49899 (p : Pattern) (ha : d21606 p = 1) (hb : d146837 p = 1) : d149045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21592 q = 1) (hb : d146837 q = 1) : d149031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49895 q ha hb
    | true =>
      simp only [d21592, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21593 q = 1) (hb : d146837 q = 1) : d149032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21594 q = 1) (hb : d146837 q = 1) : d149033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21594, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21595 q = 1) (hb : d146837 q = 1) : d149034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21596 q = 1) (hb : d146837 q = 1) : d149035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21606 q = 1) (hb : d146837 q = 1) : d149045 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21606, d149045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21606, d149045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49900 (p : Pattern) (ha : d21655 p = 1) (hb : d146837 p = 1) : d149070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21637 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45814 q ha hb
    | true =>
      simp only [d21637, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21638 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21639 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21645 q = 1) (hb : d146837 q = 1) : d149060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21645, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21654 q = 1) (hb : d146837 q = 1) : d149069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21654, d149069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21654, d149069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21655 q = 1) (hb : d146837 q = 1) : d149070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21655, d149070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21655, d149070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49901 (p : Pattern) (ha : d21715 p = 1) (hb : d146837 p = 1) : d149093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21656 q = 1) (hb : d146837 q = 1) : d149071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49900 q ha hb
    | true =>
      simp only [d21656, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21657 q = 1) (hb : d146837 q = 1) : d149072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21712 q = 1) (hb : d146837 q = 1) : d149090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21712, d149090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21712, d149090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21713 q = 1) (hb : d146837 q = 1) : d149091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21713, d149091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21713, d149091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21714 q = 1) (hb : d146837 q = 1) : d149092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21714, d149092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21714, d149092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21715 q = 1) (hb : d146837 q = 1) : d149093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21715, d149093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21715, d149093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49902 (p : Pattern) (ha : d21721 p = 1) (hb : d146837 p = 1) : d149099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21716 q = 1) (hb : d146837 q = 1) : d149094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21716, d149094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49901 q ha hb
    | true =>
      simp only [d21716, d149094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21717 q = 1) (hb : d146837 q = 1) : d149095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21717, d149095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21717, d149095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21718 q = 1) (hb : d146837 q = 1) : d149096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21718, d149096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21718, d149096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21719 q = 1) (hb : d146837 q = 1) : d149097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21719, d149097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21719, d149097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21720 q = 1) (hb : d146837 q = 1) : d149098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21720, d149098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21720, d149098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21721 q = 1) (hb : d146837 q = 1) : d149099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21721, d149099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21721, d149099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49903 (p : Pattern) (ha : d21465 p = 1) (hb : d146837 p = 1) : d148962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d146837 q = 1) : d148935 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d146837 q = 1) : d148961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21465 q = 1) (hb : d146837 q = 1) : d148962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21465, d148962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21465, d148962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49904 (p : Pattern) (ha : d21467 p = 1) (hb : d146837 p = 1) : d148964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d146837 q = 1) : d148939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d146837 q = 1) : d148963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21467 q = 1) (hb : d146837 q = 1) : d148964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21467, d148964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21467, d148964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49905 (p : Pattern) (ha : d21474 p = 1) (hb : d146837 p = 1) : d148971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d146837 q = 1) : d148969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d146837 q = 1) : d148970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21474 q = 1) (hb : d146837 q = 1) : d148971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21474, d148971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21474, d148971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49906 (p : Pattern) (ha : d21477 p = 1) (hb : d146837 p = 1) : d148974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d146837 q = 1) : d148972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d146837 q = 1) : d148973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21477 q = 1) (hb : d146837 q = 1) : d148974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21477, d148974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21477, d148974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49907 (p : Pattern) (ha : d21503 p = 1) (hb : d146837 p = 1) : d148984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21419 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21494 q = 1) (hb : d146837 q = 1) : d148979 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21494, d146837, d148979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45822 q ha hb
    | true =>
      simp only [d21494, d146837, d148979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21495 q = 1) (hb : d146837 q = 1) : d148980 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21495, d148980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21495, d148980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21496 q = 1) (hb : d146837 q = 1) : d148981 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21496, d148981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21496, d148981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21497 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21498 q = 1) (hb : d146837 q = 1) : d148791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21498, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45801 q ha hb
    | true =>
      simp only [d21498, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21499 q = 1) (hb : d146837 q = 1) : d148792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21499, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21499, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21500 q = 1) (hb : d146837 q = 1) : d148793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21500, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21500, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21501 q = 1) (hb : d146837 q = 1) : d148982 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21501, d148982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21501, d148982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21420 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d21421 q = 1) (hb : d146837 q = 1) : d148791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45801 q ha hb
    | true =>
      simp only [d21421, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d21422 q = 1) (hb : d146837 q = 1) : d148792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21423 q = 1) (hb : d146837 q = 1) : d148793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21424 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45802 q ha hb
    | true =>
      simp only [d21424, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d21425 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21426 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21427 q = 1) (hb : d146837 q = 1) : d148794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21427, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21502 q = 1) (hb : d146837 q = 1) : d148983 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21502, d148983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21502, d148983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21503 q = 1) (hb : d146837 q = 1) : d148984 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21503, d148984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21503, d148984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro49908 (p : Pattern) (ha : d21509 p = 1) (hb : d146837 p = 1) : d148990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d146837 q = 1) : d148985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49907 q ha hb
    | true =>
      simp only [d21504, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d146837 q = 1) : d148986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d146837 q = 1) : d148987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d146837 q = 1) : d148988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d146837 q = 1) : d148989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21509 q = 1) (hb : d146837 q = 1) : d148990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21509, d148990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21509, d148990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49909 (p : Pattern) (ha : d21554 p = 1) (hb : d146837 p = 1) : d148996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d146837 q = 1) : d148993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d146837 q = 1) : d148994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d146837 q = 1) : d148995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21554 q = 1) (hb : d146837 q = 1) : d148996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21554, d148996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21554, d148996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49910 (p : Pattern) (ha : d146837 p = 1) (hb : d150118 p = 1) : d149002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d146837 q = 1) : d148965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49903 q ha hb
    | true =>
      simp only [d21468, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49904 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d146837 q = 1) : d148966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d146837 q = 1) : d148967 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d146837 q = 1) : d148968 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d146837 q = 1) : d148975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49905 q ha hb
    | true =>
      simp only [d21478, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49906 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d146837 q = 1) : d148976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d146837 q = 1) : d148977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d146837 q = 1) : d148991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49908 q ha hb
    | true =>
      simp only [d21510, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49891 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150114 q = 1) : d148992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150114, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d146837 q = 1) : d148997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49909 q ha hb
    | true =>
      simp only [d21555, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d146837 q = 1) : d148998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150115 q = 1) : d148999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150116 q = 1) : d149000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150116, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150117 q = 1) : d149001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150117, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150118 q = 1) : d149002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d149002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150118, d149002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49911 (p : Pattern) (ha : d21561 p = 1) (hb : d146837 p = 1) : d149003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d146837 q = 1) : d148935 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d146837 q = 1) : d148961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21561 q = 1) (hb : d146837 q = 1) : d149003 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21561, d149003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21561, d149003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49912 (p : Pattern) (ha : d21562 p = 1) (hb : d146837 p = 1) : d149004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d146837 q = 1) : d148939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d146837 q = 1) : d148963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21562 q = 1) (hb : d146837 q = 1) : d149004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21562, d149004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21562, d149004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49913 (p : Pattern) (ha : d21567 p = 1) (hb : d146837 p = 1) : d149009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d146837 q = 1) : d148969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d146837 q = 1) : d148970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21567 q = 1) (hb : d146837 q = 1) : d149009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21567, d149009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21567, d149009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49914 (p : Pattern) (ha : d21568 p = 1) (hb : d146837 p = 1) : d149010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49890 q ha hb
    | true =>
      simp only [d21435, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d146837 q = 1) : d148972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d146837 q = 1) : d148973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21568 q = 1) (hb : d146837 q = 1) : d149010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21568, d149010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21568, d149010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49915 (p : Pattern) (ha : d21572 p = 1) (hb : d146837 p = 1) : d149014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d146837 q = 1) : d148985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49907 q ha hb
    | true =>
      simp only [d21504, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d146837 q = 1) : d148986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d146837 q = 1) : d148987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d146837 q = 1) : d148988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d146837 q = 1) : d148989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21572 q = 1) (hb : d146837 q = 1) : d149014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21572, d149014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21572, d149014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49916 (p : Pattern) (ha : d21578 p = 1) (hb : d146837 p = 1) : d149017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49889 q ha hb
    | true =>
      simp only [d21431, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d146837 q = 1) : d148993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d146837 q = 1) : d148994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d146837 q = 1) : d148995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21578 q = 1) (hb : d146837 q = 1) : d149017 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21578, d149017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21578, d149017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49917 (p : Pattern) (ha : d146837 p = 1) (hb : d150123 p = 1) : d149023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d146837 q = 1) : d148965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49903 q ha hb
    | true =>
      simp only [d21468, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49904 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d146837 q = 1) : d148966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d146837 q = 1) : d148967 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d146837 q = 1) : d148968 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d146837 q = 1) : d148975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49905 q ha hb
    | true =>
      simp only [d21478, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49906 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d146837 q = 1) : d148976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d146837 q = 1) : d148977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d146837 q = 1) : d148991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49908 q ha hb
    | true =>
      simp only [d21510, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49891 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150114 q = 1) : d148992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150114, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d146837 q = 1) : d148997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49909 q ha hb
    | true =>
      simp only [d21555, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d146837 q = 1) : d148998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150115 q = 1) : d148999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150116 q = 1) : d149000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150116, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150117 q = 1) : d149001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150117, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21563 q = 1) (hb : d146837 q = 1) : d149005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21563, d149005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49911 q ha hb
    | true =>
      simp only [d21563, d149005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49912 q ha hb
  have h16 (q : Pattern) (ha : d21564 q = 1) (hb : d146837 q = 1) : d149006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21564, d149006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21564, d149006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21565 q = 1) (hb : d146837 q = 1) : d149007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21565, d149007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21565, d149007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21566 q = 1) (hb : d146837 q = 1) : d149008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21566, d149008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21566, d149008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21569 q = 1) (hb : d146837 q = 1) : d149011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21569, d149011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49913 q ha hb
    | true =>
      simp only [d21569, d149011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49914 q ha hb
  have h20 (q : Pattern) (ha : d21570 q = 1) (hb : d146837 q = 1) : d149012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21570, d149012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21570, d149012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21571 q = 1) (hb : d146837 q = 1) : d149013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21571, d149013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21571, d149013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21573 q = 1) (hb : d146837 q = 1) : d149015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49915 q ha hb
    | true =>
      simp only [d21573, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49894 q ha hb
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150119 q = 1) : d149016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150119, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21579 q = 1) (hb : d146837 q = 1) : d149018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49916 q ha hb
    | true =>
      simp only [d21579, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21580 q = 1) (hb : d146837 q = 1) : d149019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21580, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146837 q = 1) (hb : d150120 q = 1) : d149020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150120, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146837 q = 1) (hb : d150121 q = 1) : d149021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d149021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150121, d149021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146837 q = 1) (hb : d150122 q = 1) : d149022 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d149022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150122, d149022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146837 q = 1) (hb : d150123 q = 1) : d149023 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d149023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150123, d149023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro49918 (p : Pattern) (ha : d146837 p = 1) (hb : d150130 p = 1) : d149043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21573 q = 1) (hb : d146837 q = 1) : d149015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49915 q ha hb
    | true =>
      simp only [d21573, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49894 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150119 q = 1) : d149016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150119, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21579 q = 1) (hb : d146837 q = 1) : d149018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49916 q ha hb
    | true =>
      simp only [d21579, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21580 q = 1) (hb : d146837 q = 1) : d149019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21580, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150120 q = 1) : d149020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150120, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150128 q = 1) : d149041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d149041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150128, d149041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150129 q = 1) : d149042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d149042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150129, d149042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150130 q = 1) : d149043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d149043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150130, d149043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49919 (p : Pattern) (ha : d21642 p = 1) (hb : d146837 p = 1) : d149057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21624 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21625 q = 1) (hb : d146837 q = 1) : d149052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21625, d146837, d149052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45836 q ha hb
    | true =>
      simp only [d21625, d146837, d149052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21626 q = 1) (hb : d146837 q = 1) : d149053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21626, d149053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21626, d149053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21627 q = 1) (hb : d146837 q = 1) : d149054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21627, d149054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21627, d149054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21628 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21629 q = 1) (hb : d146837 q = 1) : d148864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21629, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45837 q ha hb
    | true =>
      simp only [d21629, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21630 q = 1) (hb : d146837 q = 1) : d148865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21630, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21630, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21631 q = 1) (hb : d146837 q = 1) : d148866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21631, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21631, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21632 q = 1) (hb : d146837 q = 1) : d149055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21632, d149055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21632, d149055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21633 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d21634 q = 1) (hb : d146837 q = 1) : d148864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45837 q ha hb
    | true =>
      simp only [d21634, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d21635 q = 1) (hb : d146837 q = 1) : d148865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21636 q = 1) (hb : d146837 q = 1) : d148866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21637 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45814 q ha hb
    | true =>
      simp only [d21637, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d21638 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21639 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21640 q = 1) (hb : d146837 q = 1) : d148867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21640, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21641 q = 1) (hb : d146837 q = 1) : d149056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21641, d149056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21641, d149056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21642 q = 1) (hb : d146837 q = 1) : d149057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21642, d149057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21642, d149057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro49920 (p : Pattern) (ha : d21647 p = 1) (hb : d146837 p = 1) : d149062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21633 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21634 q = 1) (hb : d146837 q = 1) : d148864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45837 q ha hb
    | true =>
      simp only [d21634, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21635 q = 1) (hb : d146837 q = 1) : d148865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21636 q = 1) (hb : d146837 q = 1) : d148866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21637 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45814 q ha hb
    | true =>
      simp only [d21637, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21638 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21639 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21640 q = 1) (hb : d146837 q = 1) : d148867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21640, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21645 q = 1) (hb : d146837 q = 1) : d149060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21645, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21646 q = 1) (hb : d146837 q = 1) : d149061 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21646, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21646, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21647 q = 1) (hb : d146837 q = 1) : d149062 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21647, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21647, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49921 (p : Pattern) (ha : d21653 p = 1) (hb : d146837 p = 1) : d149068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21643 q = 1) (hb : d146837 q = 1) : d149058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21643, d149058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49919 q ha hb
    | true =>
      simp only [d21643, d149058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21644 q = 1) (hb : d146837 q = 1) : d149059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21644, d149059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21644, d149059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21648 q = 1) (hb : d146837 q = 1) : d149063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49920 q ha hb
    | true =>
      simp only [d21648, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21649 q = 1) (hb : d146837 q = 1) : d149064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21650 q = 1) (hb : d146837 q = 1) : d149065 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21650, d149065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21650, d149065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21651 q = 1) (hb : d146837 q = 1) : d149066 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21651, d149066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21651, d149066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21652 q = 1) (hb : d146837 q = 1) : d149067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21652, d149067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21652, d149067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21653 q = 1) (hb : d146837 q = 1) : d149068 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21653, d149068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21653, d149068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49922 (p : Pattern) (ha : d21661 p = 1) (hb : d146837 p = 1) : d149076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d146837 q = 1) : d149063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49920 q ha hb
    | true =>
      simp only [d21648, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d146837 q = 1) : d149064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21656 q = 1) (hb : d146837 q = 1) : d149071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49900 q ha hb
    | true =>
      simp only [d21656, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21657 q = 1) (hb : d146837 q = 1) : d149072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21658 q = 1) (hb : d146837 q = 1) : d149073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21658, d149073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21658, d149073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21659 q = 1) (hb : d146837 q = 1) : d149074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21659, d149074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21659, d149074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21660 q = 1) (hb : d146837 q = 1) : d149075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21660, d149075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21660, d149075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21661 q = 1) (hb : d146837 q = 1) : d149076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21661, d149076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21661, d149076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49923 (p : Pattern) (ha : d21704 p = 1) (hb : d146837 p = 1) : d149082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d146837 q = 1) : d149063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49920 q ha hb
    | true =>
      simp only [d21648, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d146837 q = 1) : d149064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21701 q = 1) (hb : d146837 q = 1) : d149079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21701, d149079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21701, d149079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21702 q = 1) (hb : d146837 q = 1) : d149080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21702, d149080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21702, d149080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21703 q = 1) (hb : d146837 q = 1) : d149081 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21703, d149081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21703, d149081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21704 q = 1) (hb : d146837 q = 1) : d149082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21704, d149082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21704, d149082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49924 (p : Pattern) (ha : d146837 p = 1) (hb : d150140 p = 1) : d149088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21662 q = 1) (hb : d146837 q = 1) : d149077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21662, d149077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49921 q ha hb
    | true =>
      simp only [d21662, d149077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49922 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150136 q = 1) : d149078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d149078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150136, d149078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21705 q = 1) (hb : d146837 q = 1) : d149083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21705, d149083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49923 q ha hb
    | true =>
      simp only [d21705, d149083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21706 q = 1) (hb : d146837 q = 1) : d149084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21706, d149084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21706, d149084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150137 q = 1) : d149085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d149085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150137, d149085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150138 q = 1) : d149086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d149086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150138, d149086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150139 q = 1) : d149087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d149087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150139, d149087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150140 q = 1) : d149088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d149088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150140, d149088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49925 (p : Pattern) (ha : d146837 p = 1) (hb : d150146 p = 1) : d149105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21451 q = 1) (hb : d146837 q = 1) : d148948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21451, d148948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21451, d148948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49893 q ha hb
  have h2 (q : Pattern) (ha : d21452 q = 1) (hb : d146837 q = 1) : d148949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21452, d148949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21452, d148949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21461 q = 1) (hb : d146837 q = 1) : d148958 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49893 q ha hb
    | true =>
      simp only [d21461, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49896 q ha hb
  have h4 (q : Pattern) (ha : d21462 q = 1) (hb : d146837 q = 1) : d148959 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21462, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21463 q = 1) (hb : d146837 q = 1) : d148960 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21463, d148960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21463, d148960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150124 q = 1) : d149024 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d149024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49910 q ha hb
    | true =>
      simp only [d150124, d149024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49917 q ha hb
  have h7 (q : Pattern) (ha : d21598 q = 1) (hb : d146837 q = 1) : d149037 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21598, d149037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49897 q ha hb
    | true =>
      simp only [d21598, d149037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49898 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150125 q = 1) : d149038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d149038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150125, d149038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150126 q = 1) : d149039 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d149039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150126, d149039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150127 q = 1) : d149040 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d149040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150127, d149040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150131 q = 1) : d149044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d149044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150131, d149044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49918 q ha hb
  have h12 (q : Pattern) (ha : d21607 q = 1) (hb : d146837 q = 1) : d149046 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21607, d149046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21607, d149046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49899 q ha hb
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150132 q = 1) : d149047 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d149047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150132, d149047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150133 q = 1) : d149048 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d149048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150133, d149048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150134 q = 1) : d149049 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d149049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150134, d149049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150135 q = 1) : d149050 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d149050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150135, d149050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150141 q = 1) : d149089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d149089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150141, d149089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49924 q ha hb
  have h18 (q : Pattern) (ha : d21722 q = 1) (hb : d146837 q = 1) : d149100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21722, d149100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21722, d149100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49902 q ha hb
  have h19 (q : Pattern) (ha : d146837 q = 1) (hb : d150142 q = 1) : d149101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d149101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150142, d149101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146837 q = 1) (hb : d150143 q = 1) : d149102 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d149102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150143, d149102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146837 q = 1) (hb : d150144 q = 1) : d149103 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d149103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150144, d149103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146837 q = 1) (hb : d150145 q = 1) : d149104 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d149104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150145, d149104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150146 q = 1) : d149105 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d149105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150146, d149105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49926 (p : Pattern) (ha : d146837 p = 1) (hb : d150152 p = 1) : d149111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150147 q = 1) : d149106 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d149106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150147, d149106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49925 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150148 q = 1) : d149107 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d149107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150148, d149107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150149 q = 1) : d149108 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d149108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150149, d149108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150150 q = 1) : d149109 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d149109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150150, d149109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150151 q = 1) : d149110 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d149110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150151, d149110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150152 q = 1) : d149111 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d149111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150152, d149111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49927 (p : Pattern) (ha : d21783 p = 1) (hb : d146837 p = 1) : d149125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21762 q = 1) (hb : d146837 q = 1) : d149115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21762, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21763 q = 1) (hb : d146837 q = 1) : d149116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21764 q = 1) (hb : d146837 q = 1) : d149117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21771 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21772 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21772, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21773 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21774 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21775 q = 1) (hb : d146837 q = 1) : d149122 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21775, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21777 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d21778 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21778, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d21779 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21780 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21781 q = 1) (hb : d146837 q = 1) : d149123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21781, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21782 q = 1) (hb : d146837 q = 1) : d149124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21782, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21782, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21783 q = 1) (hb : d146837 q = 1) : d149125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21783, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21783, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro49928 (p : Pattern) (ha : d21787 p = 1) (hb : d146837 p = 1) : d149129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21777 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21778 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21778, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21779 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21780 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21781 q = 1) (hb : d146837 q = 1) : d149123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21781, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21786 q = 1) (hb : d146837 q = 1) : d149128 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21786, d149128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21786, d149128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21787 q = 1) (hb : d146837 q = 1) : d149129 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21787, d149129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21787, d149129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49929 (p : Pattern) (ha : d21793 p = 1) (hb : d146837 p = 1) : d149135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49927 q ha hb
    | true =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d146837 q = 1) : d149134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21793 q = 1) (hb : d146837 q = 1) : d149135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21793, d149135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21793, d149135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49930 (p : Pattern) (ha : d21797 p = 1) (hb : d146837 p = 1) : d149139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d146837 q = 1) : d149137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d146837 q = 1) : d149138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21797 q = 1) (hb : d146837 q = 1) : d149139 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21797, d149139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21797, d149139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49931 (p : Pattern) (ha : d21803 p = 1) (hb : d146837 p = 1) : d149145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d146837 q = 1) : d149140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49929 q ha hb
    | true =>
      simp only [d21798, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49930 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d146837 q = 1) : d149141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d146837 q = 1) : d149142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d146837 q = 1) : d149143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d146837 q = 1) : d149144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21803 q = 1) (hb : d146837 q = 1) : d149145 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49932 (p : Pattern) (ha : d21806 p = 1) (hb : d146837 p = 1) : d149148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49927 q ha hb
    | true =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21792 q = 1) (hb : d146837 q = 1) : d149134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21792, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21792, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21806 q = 1) (hb : d146837 q = 1) : d149148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21806, d149148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21806, d149148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49933 (p : Pattern) (ha : d21807 p = 1) (hb : d146837 p = 1) : d149149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d146837 q = 1) : d149137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21796 q = 1) (hb : d146837 q = 1) : d149138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21796, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21796, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21807 q = 1) (hb : d146837 q = 1) : d149149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21807, d149149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21807, d149149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49934 (p : Pattern) (ha : d21813 p = 1) (hb : d146837 p = 1) : d149155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21798 q = 1) (hb : d146837 q = 1) : d149140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49929 q ha hb
    | true =>
      simp only [d21798, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49930 q ha hb
  have h2 (q : Pattern) (ha : d21799 q = 1) (hb : d146837 q = 1) : d149141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21799, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21800 q = 1) (hb : d146837 q = 1) : d149142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21800, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21801 q = 1) (hb : d146837 q = 1) : d149143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21801, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21802 q = 1) (hb : d146837 q = 1) : d149144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21808 q = 1) (hb : d146837 q = 1) : d149150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49932 q ha hb
    | true =>
      simp only [d21808, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49933 q ha hb
  have h7 (q : Pattern) (ha : d21809 q = 1) (hb : d146837 q = 1) : d149151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21810 q = 1) (hb : d146837 q = 1) : d149152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21810, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21811 q = 1) (hb : d146837 q = 1) : d149153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21812 q = 1) (hb : d146837 q = 1) : d149154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21813 q = 1) (hb : d146837 q = 1) : d149155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21813, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49935 (p : Pattern) (ha : d21867 p = 1) (hb : d146837 p = 1) : d149125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21762 q = 1) (hb : d146837 q = 1) : d149115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21762, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21763 q = 1) (hb : d146837 q = 1) : d149116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21764 q = 1) (hb : d146837 q = 1) : d149117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21771 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21772 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21772, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21773 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21774 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21775 q = 1) (hb : d146837 q = 1) : d149122 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21775, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21865 q = 1) (hb : d146837 q = 1) : d149123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21865, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21865, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21866 q = 1) (hb : d146837 q = 1) : d149124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21866, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21866, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21867 q = 1) (hb : d146837 q = 1) : d149125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21867, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21867, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49936 (p : Pattern) (ha : d21877 p = 1) (hb : d146837 p = 1) : d149135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49935 q ha hb
    | true =>
      simp only [d21868, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d146837 q = 1) : d149134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21877 q = 1) (hb : d146837 q = 1) : d149135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21877, d149135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21877, d149135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49937 (p : Pattern) (ha : d22003 p = 1) (hb : d146837 p = 1) : d149228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21993 q = 1) (hb : d146837 q = 1) : d149140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21993, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49936 q ha hb
    | true =>
      simp only [d21993, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49930 q ha hb
  have h2 (q : Pattern) (ha : d21994 q = 1) (hb : d146837 q = 1) : d149141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21994, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21994, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21995 q = 1) (hb : d146837 q = 1) : d149142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21995, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21995, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21996 q = 1) (hb : d146837 q = 1) : d149143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21996, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21996, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21997 q = 1) (hb : d146837 q = 1) : d149144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21997, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21997, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21998 q = 1) (hb : d146837 q = 1) : d149223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49930 q ha hb
    | true =>
      simp only [d21998, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21999 q = 1) (hb : d146837 q = 1) : d149224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22000 q = 1) (hb : d146837 q = 1) : d149225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22000, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22001 q = 1) (hb : d146837 q = 1) : d149226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22002 q = 1) (hb : d146837 q = 1) : d149227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22003 q = 1) (hb : d146837 q = 1) : d149228 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22003, d149228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22003, d149228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49938 (p : Pattern) (ha : d22009 p = 1) (hb : d146837 p = 1) : d149234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21998 q = 1) (hb : d146837 q = 1) : d149223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21998, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49930 q ha hb
    | true =>
      simp only [d21998, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21999 q = 1) (hb : d146837 q = 1) : d149224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21999, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21999, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22000 q = 1) (hb : d146837 q = 1) : d149225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22000, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22000, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22001 q = 1) (hb : d146837 q = 1) : d149226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22001, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22001, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22002 q = 1) (hb : d146837 q = 1) : d149227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22002, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22002, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22004 q = 1) (hb : d146837 q = 1) : d149229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49933 q ha hb
    | true =>
      simp only [d22004, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22005 q = 1) (hb : d146837 q = 1) : d149230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22006 q = 1) (hb : d146837 q = 1) : d149231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22006, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22007 q = 1) (hb : d146837 q = 1) : d149232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22008 q = 1) (hb : d146837 q = 1) : d149233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22009 q = 1) (hb : d146837 q = 1) : d149234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22009, d149234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22009, d149234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49939 (p : Pattern) (ha : d22018 p = 1) (hb : d146837 p = 1) : d149243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22004 q = 1) (hb : d146837 q = 1) : d149229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22004, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49933 q ha hb
    | true =>
      simp only [d22004, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22005 q = 1) (hb : d146837 q = 1) : d149230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22005, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22005, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22006 q = 1) (hb : d146837 q = 1) : d149231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22006, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22006, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22007 q = 1) (hb : d146837 q = 1) : d149232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22007, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22007, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22008 q = 1) (hb : d146837 q = 1) : d149233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22008, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22008, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22018 q = 1) (hb : d146837 q = 1) : d149243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22018, d149243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22018, d149243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49940 (p : Pattern) (ha : d22103 p = 1) (hb : d146837 p = 1) : d149277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22097 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22098 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22098, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22099 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22100 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22101 q = 1) (hb : d146837 q = 1) : d149267 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22101, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22102 q = 1) (hb : d146837 q = 1) : d149276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22102, d149276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22102, d149276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22103 q = 1) (hb : d146837 q = 1) : d149277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22103, d149277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22103, d149277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49941 (p : Pattern) (ha : d22197 p = 1) (hb : d146837 p = 1) : d149300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22104 q = 1) (hb : d146837 q = 1) : d149278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49940 q ha hb
    | true =>
      simp only [d22104, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22105 q = 1) (hb : d146837 q = 1) : d149279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22194 q = 1) (hb : d146837 q = 1) : d149297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22194, d149297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22194, d149297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22195 q = 1) (hb : d146837 q = 1) : d149298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22195, d149298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22195, d149298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22196 q = 1) (hb : d146837 q = 1) : d149299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22196, d149299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22196, d149299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22197 q = 1) (hb : d146837 q = 1) : d149300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22197, d149300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22197, d149300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49942 (p : Pattern) (ha : d22203 p = 1) (hb : d146837 p = 1) : d149306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22198 q = 1) (hb : d146837 q = 1) : d149301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22198, d149301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49941 q ha hb
    | true =>
      simp only [d22198, d149301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22199 q = 1) (hb : d146837 q = 1) : d149302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22199, d149302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22199, d149302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22200 q = 1) (hb : d146837 q = 1) : d149303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22200, d149303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22200, d149303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22201 q = 1) (hb : d146837 q = 1) : d149304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22201, d149304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22201, d149304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22202 q = 1) (hb : d146837 q = 1) : d149305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22202, d149305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22202, d149305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22203 q = 1) (hb : d146837 q = 1) : d149306 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22203, d149306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22203, d149306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49943 (p : Pattern) (ha : d21818 p = 1) (hb : d146837 p = 1) : d149160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49927 q ha hb
    | true =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d146837 q = 1) : d149159 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21818 q = 1) (hb : d146837 q = 1) : d149160 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21818, d149160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21818, d149160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49944 (p : Pattern) (ha : d21820 p = 1) (hb : d146837 p = 1) : d149162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d146837 q = 1) : d149137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d146837 q = 1) : d149161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21820 q = 1) (hb : d146837 q = 1) : d149162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21820, d149162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21820, d149162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49945 (p : Pattern) (ha : d21827 p = 1) (hb : d146837 p = 1) : d149169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49927 q ha hb
    | true =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d146837 q = 1) : d149167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d146837 q = 1) : d149168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21827 q = 1) (hb : d146837 q = 1) : d149169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21827, d149169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21827, d149169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49946 (p : Pattern) (ha : d21830 p = 1) (hb : d146837 p = 1) : d149172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d146837 q = 1) : d149170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d146837 q = 1) : d149171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21830 q = 1) (hb : d146837 q = 1) : d149172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21830, d149172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21830, d149172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49947 (p : Pattern) (ha : d21862 p = 1) (hb : d146837 p = 1) : d149182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21847 q = 1) (hb : d146837 q = 1) : d149177 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21847, d146837, d149177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45873 q ha hb
    | true =>
      simp only [d21847, d146837, d149177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21848 q = 1) (hb : d146837 q = 1) : d149178 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21848, d149178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21848, d149178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21849 q = 1) (hb : d146837 q = 1) : d149179 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21849, d149179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21849, d149179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21856 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21857 q = 1) (hb : d146837 q = 1) : d149115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21857, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21857, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21858 q = 1) (hb : d146837 q = 1) : d149116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21858, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21858, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21859 q = 1) (hb : d146837 q = 1) : d149117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21859, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21859, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21860 q = 1) (hb : d146837 q = 1) : d149180 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21860, d149180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21860, d149180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21761 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d21762 q = 1) (hb : d146837 q = 1) : d149115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21762, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d21763 q = 1) (hb : d146837 q = 1) : d149116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21764 q = 1) (hb : d146837 q = 1) : d149117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21771 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21772 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21772, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d21773 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21774 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21775 q = 1) (hb : d146837 q = 1) : d149122 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21775, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21861 q = 1) (hb : d146837 q = 1) : d149181 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21861, d149181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21861, d149181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21862 q = 1) (hb : d146837 q = 1) : d149182 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21862, d149182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21862, d149182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro49948 (p : Pattern) (ha : d21873 p = 1) (hb : d146837 p = 1) : d149188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d146837 q = 1) : d149183 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49947 q ha hb
    | true =>
      simp only [d21863, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d146837 q = 1) : d149184 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49935 q ha hb
    | true =>
      simp only [d21868, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d146837 q = 1) : d149185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d146837 q = 1) : d149186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d146837 q = 1) : d149187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21873 q = 1) (hb : d146837 q = 1) : d149188 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21873, d149188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21873, d149188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49949 (p : Pattern) (ha : d21954 p = 1) (hb : d146837 p = 1) : d149125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21762 q = 1) (hb : d146837 q = 1) : d149115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45847 q ha hb
    | true =>
      simp only [d21762, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21763 q = 1) (hb : d146837 q = 1) : d149116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21764 q = 1) (hb : d146837 q = 1) : d149117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21771 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21772 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21772, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21773 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21774 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21775 q = 1) (hb : d146837 q = 1) : d149122 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21775, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21948 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d21949 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21949, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45848 q ha hb
    | true =>
      simp only [d21949, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d21950 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21950, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21950, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21951 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21951, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21951, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21952 q = 1) (hb : d146837 q = 1) : d149123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21952, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21952, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21953 q = 1) (hb : d146837 q = 1) : d149124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21953, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21953, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21954 q = 1) (hb : d146837 q = 1) : d149125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21954, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21954, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro49950 (p : Pattern) (ha : d21960 p = 1) (hb : d146837 p = 1) : d149194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49949 q ha hb
    | true =>
      simp only [d21955, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d146837 q = 1) : d149191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d146837 q = 1) : d149192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d146837 q = 1) : d149193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21960 q = 1) (hb : d146837 q = 1) : d149194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21960, d149194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21960, d149194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49951 (p : Pattern) (ha : d146837 p = 1) (hb : d150159 p = 1) : d149200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d146837 q = 1) : d149163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49943 q ha hb
    | true =>
      simp only [d21821, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49944 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d146837 q = 1) : d149164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d146837 q = 1) : d149165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d146837 q = 1) : d149166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d146837 q = 1) : d149173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49945 q ha hb
    | true =>
      simp only [d21831, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49946 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d146837 q = 1) : d149174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d146837 q = 1) : d149175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d146837 q = 1) : d149189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49948 q ha hb
    | true =>
      simp only [d21878, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49936 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150155 q = 1) : d149190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150155, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d146837 q = 1) : d149195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49950 q ha hb
    | true =>
      simp only [d21961, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d146837 q = 1) : d149196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150156 q = 1) : d149197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150157 q = 1) : d149198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150157, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150158 q = 1) : d149199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150158, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150159 q = 1) : d149200 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150159, d149200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150159, d149200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49952 (p : Pattern) (ha : d21967 p = 1) (hb : d146837 p = 1) : d149201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49927 q ha hb
    | true =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21791 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21791, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21791, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21817 q = 1) (hb : d146837 q = 1) : d149159 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21817, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21817, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21967 q = 1) (hb : d146837 q = 1) : d149201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21967, d149201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21967, d149201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49953 (p : Pattern) (ha : d21968 p = 1) (hb : d146837 p = 1) : d149202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21795 q = 1) (hb : d146837 q = 1) : d149137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21795, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21795, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21819 q = 1) (hb : d146837 q = 1) : d149161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21819, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21819, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21968 q = 1) (hb : d146837 q = 1) : d149202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21968, d149202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21968, d149202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49954 (p : Pattern) (ha : d21973 p = 1) (hb : d146837 p = 1) : d149207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21784 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49927 q ha hb
    | true =>
      simp only [d21784, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21785 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21785, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21790 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21790, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21825 q = 1) (hb : d146837 q = 1) : d149167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21825, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21825, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21826 q = 1) (hb : d146837 q = 1) : d149168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21826, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21826, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21973 q = 1) (hb : d146837 q = 1) : d149207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21973, d149207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21973, d149207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49955 (p : Pattern) (ha : d21974 p = 1) (hb : d146837 p = 1) : d149208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21794 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21794, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21828 q = 1) (hb : d146837 q = 1) : d149170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21828, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21828, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21829 q = 1) (hb : d146837 q = 1) : d149171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21829, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21829, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21974 q = 1) (hb : d146837 q = 1) : d149208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21974, d149208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21974, d149208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49956 (p : Pattern) (ha : d21978 p = 1) (hb : d146837 p = 1) : d149212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21863 q = 1) (hb : d146837 q = 1) : d149183 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21863, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49947 q ha hb
    | true =>
      simp only [d21863, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21864 q = 1) (hb : d146837 q = 1) : d149184 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21864, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21864, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21868 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49935 q ha hb
    | true =>
      simp only [d21868, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21869 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21870 q = 1) (hb : d146837 q = 1) : d149185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21870, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21870, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21871 q = 1) (hb : d146837 q = 1) : d149186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21871, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21871, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21872 q = 1) (hb : d146837 q = 1) : d149187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21872, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21872, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21978 q = 1) (hb : d146837 q = 1) : d149212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21978, d149212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21978, d149212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49957 (p : Pattern) (ha : d21979 p = 1) (hb : d146837 p = 1) : d149148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21868 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21868, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49935 q ha hb
    | true =>
      simp only [d21868, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21869 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21869, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21869, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21788 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49928 q ha hb
    | true =>
      simp only [d21788, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21789 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21789, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21874 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21874, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21874, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21875 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21875, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21875, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21876 q = 1) (hb : d146837 q = 1) : d149134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21876, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21876, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21979 q = 1) (hb : d146837 q = 1) : d149148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21979, d149148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21979, d149148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49958 (p : Pattern) (ha : d21985 p = 1) (hb : d146837 p = 1) : d149215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21955 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21955, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49949 q ha hb
    | true =>
      simp only [d21955, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21956 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21956, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21956, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21957 q = 1) (hb : d146837 q = 1) : d149191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21957, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21957, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21958 q = 1) (hb : d146837 q = 1) : d149192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21958, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21958, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21959 q = 1) (hb : d146837 q = 1) : d149193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21959, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21959, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21985 q = 1) (hb : d146837 q = 1) : d149215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21985, d149215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21985, d149215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49959 (p : Pattern) (ha : d146837 p = 1) (hb : d150164 p = 1) : d149221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21821 q = 1) (hb : d146837 q = 1) : d149163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21821, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49943 q ha hb
    | true =>
      simp only [d21821, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49944 q ha hb
  have h2 (q : Pattern) (ha : d21822 q = 1) (hb : d146837 q = 1) : d149164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21822, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21822, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21823 q = 1) (hb : d146837 q = 1) : d149165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21823, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21823, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21824 q = 1) (hb : d146837 q = 1) : d149166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21824, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21824, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21831 q = 1) (hb : d146837 q = 1) : d149173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21831, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49945 q ha hb
    | true =>
      simp only [d21831, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49946 q ha hb
  have h6 (q : Pattern) (ha : d21832 q = 1) (hb : d146837 q = 1) : d149174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21832, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21832, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21833 q = 1) (hb : d146837 q = 1) : d149175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21833, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21833, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21878 q = 1) (hb : d146837 q = 1) : d149189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21878, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49948 q ha hb
    | true =>
      simp only [d21878, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49936 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150155 q = 1) : d149190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150155, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21961 q = 1) (hb : d146837 q = 1) : d149195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21961, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49950 q ha hb
    | true =>
      simp only [d21961, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21962 q = 1) (hb : d146837 q = 1) : d149196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21962, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21962, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150156 q = 1) : d149197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150156, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150157 q = 1) : d149198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150157, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150158 q = 1) : d149199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150158, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21969 q = 1) (hb : d146837 q = 1) : d149203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21969, d149203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49952 q ha hb
    | true =>
      simp only [d21969, d149203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49953 q ha hb
  have h16 (q : Pattern) (ha : d21970 q = 1) (hb : d146837 q = 1) : d149204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21970, d149204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21970, d149204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21971 q = 1) (hb : d146837 q = 1) : d149205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21971, d149205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21971, d149205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21972 q = 1) (hb : d146837 q = 1) : d149206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21972, d149206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21972, d149206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21975 q = 1) (hb : d146837 q = 1) : d149209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21975, d149209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49954 q ha hb
    | true =>
      simp only [d21975, d149209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49955 q ha hb
  have h20 (q : Pattern) (ha : d21976 q = 1) (hb : d146837 q = 1) : d149210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21976, d149210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21976, d149210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21977 q = 1) (hb : d146837 q = 1) : d149211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21977, d149211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21977, d149211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21980 q = 1) (hb : d146837 q = 1) : d149213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49956 q ha hb
    | true =>
      simp only [d21980, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49957 q ha hb
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150160 q = 1) : d149214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150160, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21986 q = 1) (hb : d146837 q = 1) : d149216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49958 q ha hb
    | true =>
      simp only [d21986, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21987 q = 1) (hb : d146837 q = 1) : d149217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21987, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d146837 q = 1) (hb : d150161 q = 1) : d149218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150161, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d146837 q = 1) (hb : d150162 q = 1) : d149219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150162, d149219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150162, d149219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d146837 q = 1) (hb : d150163 q = 1) : d149220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150163, d149220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150163, d149220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146837 q = 1) (hb : d150164 q = 1) : d149221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150164, d149221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150164, d149221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro49960 (p : Pattern) (ha : d146837 p = 1) (hb : d150171 p = 1) : d149241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21980 q = 1) (hb : d146837 q = 1) : d149213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21980, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49956 q ha hb
    | true =>
      simp only [d21980, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49957 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150160 q = 1) : d149214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150160, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21986 q = 1) (hb : d146837 q = 1) : d149216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21986, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49958 q ha hb
    | true =>
      simp only [d21986, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21987 q = 1) (hb : d146837 q = 1) : d149217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21987, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21987, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150161 q = 1) : d149218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150161, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150169 q = 1) : d149239 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150169, d149239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150169, d149239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150170 q = 1) : d149240 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150170, d149240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150170, d149240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150171 q = 1) : d149241 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d149241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150171, d149241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49961 (p : Pattern) (ha : d22084 p = 1) (hb : d146837 p = 1) : d149264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22049 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22050 q = 1) (hb : d146837 q = 1) : d149250 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22050, d146837, d149250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45889 q ha hb
    | true =>
      simp only [d22050, d146837, d149250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22051 q = 1) (hb : d146837 q = 1) : d149251 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22051, d149251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22051, d149251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22052 q = 1) (hb : d146837 q = 1) : d149252 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22052, d149252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22052, d149252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22059 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22060 q = 1) (hb : d146837 q = 1) : d149254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22060, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22060, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22061 q = 1) (hb : d146837 q = 1) : d149255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22061, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22061, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22062 q = 1) (hb : d146837 q = 1) : d149256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22062, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22062, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22063 q = 1) (hb : d146837 q = 1) : d149257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22063, d149257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22063, d149257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22069 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22070 q = 1) (hb : d146837 q = 1) : d149254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22070, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22071 q = 1) (hb : d146837 q = 1) : d149255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22072 q = 1) (hb : d146837 q = 1) : d149256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22078 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22079 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22079, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d22080 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22081 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22082 q = 1) (hb : d146837 q = 1) : d149262 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22082, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22083 q = 1) (hb : d146837 q = 1) : d149263 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22083, d149263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22083, d149263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d22084 q = 1) (hb : d146837 q = 1) : d149264 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22084, d149264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22084, d149264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro49962 (p : Pattern) (ha : d22089 p = 1) (hb : d146837 p = 1) : d149269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22070 q = 1) (hb : d146837 q = 1) : d149254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22070, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22071 q = 1) (hb : d146837 q = 1) : d149255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22072 q = 1) (hb : d146837 q = 1) : d149256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22078 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22079 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22079, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22080 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22081 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22082 q = 1) (hb : d146837 q = 1) : d149262 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22082, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22087 q = 1) (hb : d146837 q = 1) : d149267 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22087, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22087, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22088 q = 1) (hb : d146837 q = 1) : d149268 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22088, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22088, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22089 q = 1) (hb : d146837 q = 1) : d149269 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22089, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22089, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49963 (p : Pattern) (ha : d22095 p = 1) (hb : d146837 p = 1) : d149275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22085 q = 1) (hb : d146837 q = 1) : d149265 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22085, d149265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49961 q ha hb
    | true =>
      simp only [d22085, d149265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22086 q = 1) (hb : d146837 q = 1) : d149266 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22086, d149266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22086, d149266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22090 q = 1) (hb : d146837 q = 1) : d149270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49962 q ha hb
    | true =>
      simp only [d22090, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22091 q = 1) (hb : d146837 q = 1) : d149271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22092 q = 1) (hb : d146837 q = 1) : d149272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22092, d149272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22092, d149272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22093 q = 1) (hb : d146837 q = 1) : d149273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22093, d149273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22093, d149273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22094 q = 1) (hb : d146837 q = 1) : d149274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22094, d149274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22094, d149274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22095 q = 1) (hb : d146837 q = 1) : d149275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22095, d149275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22095, d149275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49964 (p : Pattern) (ha : d22109 p = 1) (hb : d146837 p = 1) : d149283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22090 q = 1) (hb : d146837 q = 1) : d149270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22090, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49962 q ha hb
    | true =>
      simp only [d22090, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22091 q = 1) (hb : d146837 q = 1) : d149271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22091, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22091, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d146837 q = 1) : d149278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49940 q ha hb
    | true =>
      simp only [d22104, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d146837 q = 1) : d149279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22106 q = 1) (hb : d146837 q = 1) : d149280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22106, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22106, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22107 q = 1) (hb : d146837 q = 1) : d149281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22107, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22107, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22108 q = 1) (hb : d146837 q = 1) : d149282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22108, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22108, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22109 q = 1) (hb : d146837 q = 1) : d149283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22109, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22109, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49965 (p : Pattern) (ha : d22180 p = 1) (hb : d146837 p = 1) : d149269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22070 q = 1) (hb : d146837 q = 1) : d149254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45890 q ha hb
    | true =>
      simp only [d22070, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22071 q = 1) (hb : d146837 q = 1) : d149255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22072 q = 1) (hb : d146837 q = 1) : d149256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22078 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22079 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22079, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22080 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22081 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22082 q = 1) (hb : d146837 q = 1) : d149262 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22082, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22174 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22175 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22175, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22175, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22176 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22176, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22176, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22177 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22177, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22177, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22178 q = 1) (hb : d146837 q = 1) : d149267 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22178, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22178, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22179 q = 1) (hb : d146837 q = 1) : d149268 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22179, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22179, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22180 q = 1) (hb : d146837 q = 1) : d149269 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22180, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22180, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro49966 (p : Pattern) (ha : d22186 p = 1) (hb : d146837 p = 1) : d149289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22181 q = 1) (hb : d146837 q = 1) : d149270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22181, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49965 q ha hb
    | true =>
      simp only [d22181, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22182 q = 1) (hb : d146837 q = 1) : d149271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22182, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22182, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22183 q = 1) (hb : d146837 q = 1) : d149286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22183, d149286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22183, d149286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22184 q = 1) (hb : d146837 q = 1) : d149287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22184, d149287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22184, d149287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22185 q = 1) (hb : d146837 q = 1) : d149288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22185, d149288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22185, d149288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22186 q = 1) (hb : d146837 q = 1) : d149289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22186, d149289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22186, d149289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49967 (p : Pattern) (ha : d146837 p = 1) (hb : d150181 p = 1) : d149295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22110 q = 1) (hb : d146837 q = 1) : d149284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22110, d149284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49963 q ha hb
    | true =>
      simp only [d22110, d149284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49964 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150177 q = 1) : d149285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d149285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150177, d149285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d22187 q = 1) (hb : d146837 q = 1) : d149290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22187, d149290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49966 q ha hb
    | true =>
      simp only [d22187, d149290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22188 q = 1) (hb : d146837 q = 1) : d149291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22188, d149291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22188, d149291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150178 q = 1) : d149292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d149292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150178, d149292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150179 q = 1) : d149293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d149293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150179, d149293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146837 q = 1) (hb : d150180 q = 1) : d149294 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d149294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150180, d149294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150181 q = 1) : d149295 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d149295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150181, d149295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49968 (p : Pattern) (ha : d146837 p = 1) (hb : d150187 p = 1) : d149312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21804 q = 1) (hb : d146837 q = 1) : d149146 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21804, d149146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21804, d149146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49931 q ha hb
  have h2 (q : Pattern) (ha : d21805 q = 1) (hb : d146837 q = 1) : d149147 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21805, d149147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21805, d149147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21814 q = 1) (hb : d146837 q = 1) : d149156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49931 q ha hb
    | true =>
      simp only [d21814, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49934 q ha hb
  have h4 (q : Pattern) (ha : d21815 q = 1) (hb : d146837 q = 1) : d149157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21815, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21816 q = 1) (hb : d146837 q = 1) : d149158 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21816, d149158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21816, d149158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150165 q = 1) : d149222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150165, d149222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49951 q ha hb
    | true =>
      simp only [d150165, d149222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49959 q ha hb
  have h7 (q : Pattern) (ha : d22010 q = 1) (hb : d146837 q = 1) : d149235 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22010, d149235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49937 q ha hb
    | true =>
      simp only [d22010, d149235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49938 q ha hb
  have h8 (q : Pattern) (ha : d146837 q = 1) (hb : d150166 q = 1) : d149236 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150166, d149236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150166, d149236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150167 q = 1) : d149237 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d149237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150167, d149237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146837 q = 1) (hb : d150168 q = 1) : d149238 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d149238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150168, d149238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146837 q = 1) (hb : d150172 q = 1) : d149242 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d149242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150172, d149242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49960 q ha hb
  have h12 (q : Pattern) (ha : d22019 q = 1) (hb : d146837 q = 1) : d149244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22019, d149244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22019, d149244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49939 q ha hb
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150173 q = 1) : d149245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d149245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150173, d149245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150174 q = 1) : d149246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d149246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150174, d149246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150175 q = 1) : d149247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d149247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150175, d149247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146837 q = 1) (hb : d150176 q = 1) : d149248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d149248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150176, d149248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146837 q = 1) (hb : d150182 q = 1) : d149296 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d149296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150182, d149296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49967 q ha hb
  have h18 (q : Pattern) (ha : d22204 q = 1) (hb : d146837 q = 1) : d149307 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22204, d149307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22204, d149307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49942 q ha hb
  have h19 (q : Pattern) (ha : d146837 q = 1) (hb : d150183 q = 1) : d149308 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d149308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150183, d149308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d146837 q = 1) (hb : d150184 q = 1) : d149309 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d149309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150184, d149309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146837 q = 1) (hb : d150185 q = 1) : d149310 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d149310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150185, d149310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d146837 q = 1) (hb : d150186 q = 1) : d149311 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d149311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150186, d149311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146837 q = 1) (hb : d150187 q = 1) : d149312 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d149312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150187, d149312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49969 (p : Pattern) (ha : d146837 p = 1) (hb : d150193 p = 1) : d149318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146837 q = 1) (hb : d150188 q = 1) : d149313 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d149313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150188, d149313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49968 q ha hb
  have h2 (q : Pattern) (ha : d146837 q = 1) (hb : d150189 q = 1) : d149314 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d149314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150189, d149314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146837 q = 1) (hb : d150190 q = 1) : d149315 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d149315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150190, d149315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146837 q = 1) (hb : d150191 q = 1) : d149316 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d149316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150191, d149316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146837 q = 1) (hb : d150192 q = 1) : d149317 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d149317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150192, d149317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146837 q = 1) (hb : d150193 q = 1) : d149318 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d149318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150193, d149318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49970 (p : Pattern) (ha : d22261 p = 1) (hb : d146837 p = 1) : d149333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22240 q = 1) (hb : d146837 q = 1) : d149323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22240, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22241 q = 1) (hb : d146837 q = 1) : d149324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22242 q = 1) (hb : d146837 q = 1) : d149325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22249 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22250 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22250, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22251 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22252 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22253 q = 1) (hb : d146837 q = 1) : d149330 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22253, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22255 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22256 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22256, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22257 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22258 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22259 q = 1) (hb : d146837 q = 1) : d149331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22259, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22260 q = 1) (hb : d146837 q = 1) : d149332 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22260, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22260, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22261 q = 1) (hb : d146837 q = 1) : d149333 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22261, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22261, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro49971 (p : Pattern) (ha : d22265 p = 1) (hb : d146837 p = 1) : d149337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22256 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22256, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22256, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22257 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22257, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22257, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22258 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22258, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22258, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22259 q = 1) (hb : d146837 q = 1) : d149331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22259, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22259, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22264 q = 1) (hb : d146837 q = 1) : d149336 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22264, d149336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22264, d149336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22265 q = 1) (hb : d146837 q = 1) : d149337 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22265, d149337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22265, d149337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49972 (p : Pattern) (ha : d22271 p = 1) (hb : d146837 p = 1) : d149343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49970 q ha hb
    | true =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d146837 q = 1) : d149342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22271 q = 1) (hb : d146837 q = 1) : d149343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22271, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22271, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49973 (p : Pattern) (ha : d22275 p = 1) (hb : d146837 p = 1) : d149347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d146837 q = 1) : d149345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d146837 q = 1) : d149346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22275 q = 1) (hb : d146837 q = 1) : d149347 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22275, d149347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22275, d149347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49974 (p : Pattern) (ha : d22281 p = 1) (hb : d146837 p = 1) : d149353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d146837 q = 1) : d149348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49972 q ha hb
    | true =>
      simp only [d22276, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49973 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d146837 q = 1) : d149349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d146837 q = 1) : d149350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d146837 q = 1) : d149351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d146837 q = 1) : d149352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22281 q = 1) (hb : d146837 q = 1) : d149353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22281, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22281, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49975 (p : Pattern) (ha : d22284 p = 1) (hb : d146837 p = 1) : d149356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49970 q ha hb
    | true =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22270 q = 1) (hb : d146837 q = 1) : d149342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22270, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22270, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22284 q = 1) (hb : d146837 q = 1) : d149356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22284, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22284, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49976 (p : Pattern) (ha : d22285 p = 1) (hb : d146837 p = 1) : d149357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d146837 q = 1) : d149345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22274 q = 1) (hb : d146837 q = 1) : d149346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22274, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22274, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22285 q = 1) (hb : d146837 q = 1) : d149357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22285, d149357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22285, d149357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49977 (p : Pattern) (ha : d22291 p = 1) (hb : d146837 p = 1) : d149363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22276 q = 1) (hb : d146837 q = 1) : d149348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49972 q ha hb
    | true =>
      simp only [d22276, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49973 q ha hb
  have h2 (q : Pattern) (ha : d22277 q = 1) (hb : d146837 q = 1) : d149349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22277, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22278 q = 1) (hb : d146837 q = 1) : d149350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22278, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22279 q = 1) (hb : d146837 q = 1) : d149351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22279, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22280 q = 1) (hb : d146837 q = 1) : d149352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22286 q = 1) (hb : d146837 q = 1) : d149358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49975 q ha hb
    | true =>
      simp only [d22286, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49976 q ha hb
  have h7 (q : Pattern) (ha : d22287 q = 1) (hb : d146837 q = 1) : d149359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22288 q = 1) (hb : d146837 q = 1) : d149360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22288, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22289 q = 1) (hb : d146837 q = 1) : d149361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22290 q = 1) (hb : d146837 q = 1) : d149362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22291 q = 1) (hb : d146837 q = 1) : d149363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22291, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22291, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49978 (p : Pattern) (ha : d22340 p = 1) (hb : d146837 p = 1) : d149333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22240 q = 1) (hb : d146837 q = 1) : d149323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22240, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22241 q = 1) (hb : d146837 q = 1) : d149324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22242 q = 1) (hb : d146837 q = 1) : d149325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22249 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22250 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22250, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22251 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22252 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22253 q = 1) (hb : d146837 q = 1) : d149330 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22253, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22338 q = 1) (hb : d146837 q = 1) : d149331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22338, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22338, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22339 q = 1) (hb : d146837 q = 1) : d149332 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22339, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22339, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22340 q = 1) (hb : d146837 q = 1) : d149333 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22340, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22340, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49979 (p : Pattern) (ha : d22350 p = 1) (hb : d146837 p = 1) : d149343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22341 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49978 q ha hb
    | true =>
      simp only [d22341, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22342 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22347 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22347, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22347, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22348 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22348, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22348, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22349 q = 1) (hb : d146837 q = 1) : d149342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22349, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22349, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22350 q = 1) (hb : d146837 q = 1) : d149343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22350, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22350, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49980 (p : Pattern) (ha : d22476 p = 1) (hb : d146837 p = 1) : d149436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22466 q = 1) (hb : d146837 q = 1) : d149348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22466, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49979 q ha hb
    | true =>
      simp only [d22466, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49973 q ha hb
  have h2 (q : Pattern) (ha : d22467 q = 1) (hb : d146837 q = 1) : d149349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22467, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22467, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22468 q = 1) (hb : d146837 q = 1) : d149350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22468, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22468, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22469 q = 1) (hb : d146837 q = 1) : d149351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22469, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22469, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22470 q = 1) (hb : d146837 q = 1) : d149352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22470, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22470, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22471 q = 1) (hb : d146837 q = 1) : d149431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49973 q ha hb
    | true =>
      simp only [d22471, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22472 q = 1) (hb : d146837 q = 1) : d149432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22473 q = 1) (hb : d146837 q = 1) : d149433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22473, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22474 q = 1) (hb : d146837 q = 1) : d149434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22475 q = 1) (hb : d146837 q = 1) : d149435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22476 q = 1) (hb : d146837 q = 1) : d149436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22476, d149436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22476, d149436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49981 (p : Pattern) (ha : d22482 p = 1) (hb : d146837 p = 1) : d149442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22471 q = 1) (hb : d146837 q = 1) : d149431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22471, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49973 q ha hb
    | true =>
      simp only [d22471, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22472 q = 1) (hb : d146837 q = 1) : d149432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22472, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22472, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22473 q = 1) (hb : d146837 q = 1) : d149433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22473, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22473, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22474 q = 1) (hb : d146837 q = 1) : d149434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22474, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22474, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22475 q = 1) (hb : d146837 q = 1) : d149435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22475, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22475, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22477 q = 1) (hb : d146837 q = 1) : d149437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49976 q ha hb
    | true =>
      simp only [d22477, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22478 q = 1) (hb : d146837 q = 1) : d149438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22479 q = 1) (hb : d146837 q = 1) : d149439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22479, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22480 q = 1) (hb : d146837 q = 1) : d149440 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22481 q = 1) (hb : d146837 q = 1) : d149441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22482 q = 1) (hb : d146837 q = 1) : d149442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22482, d149442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22482, d149442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49982 (p : Pattern) (ha : d22491 p = 1) (hb : d146837 p = 1) : d149451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22477 q = 1) (hb : d146837 q = 1) : d149437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22477, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49976 q ha hb
    | true =>
      simp only [d22477, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22478 q = 1) (hb : d146837 q = 1) : d149438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22478, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22478, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22479 q = 1) (hb : d146837 q = 1) : d149439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22479, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22479, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22480 q = 1) (hb : d146837 q = 1) : d149440 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22480, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22480, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22481 q = 1) (hb : d146837 q = 1) : d149441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22481, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22481, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22491 q = 1) (hb : d146837 q = 1) : d149451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22491, d149451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22491, d149451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49983 (p : Pattern) (ha : d22568 p = 1) (hb : d146837 p = 1) : d149485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22562 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22563 q = 1) (hb : d146837 q = 1) : d149467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22563, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22564 q = 1) (hb : d146837 q = 1) : d149468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22565 q = 1) (hb : d146837 q = 1) : d149469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22566 q = 1) (hb : d146837 q = 1) : d149475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22566, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22567 q = 1) (hb : d146837 q = 1) : d149484 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22567, d149484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22567, d149484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22568 q = 1) (hb : d146837 q = 1) : d149485 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22568, d149485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22568, d149485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49984 (p : Pattern) (ha : d22662 p = 1) (hb : d146837 p = 1) : d149508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22569 q = 1) (hb : d146837 q = 1) : d149486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49983 q ha hb
    | true =>
      simp only [d22569, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22570 q = 1) (hb : d146837 q = 1) : d149487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22659 q = 1) (hb : d146837 q = 1) : d149505 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22659, d149505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22659, d149505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22660 q = 1) (hb : d146837 q = 1) : d149506 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22660, d149506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22660, d149506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22661 q = 1) (hb : d146837 q = 1) : d149507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22661, d149507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22661, d149507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22662 q = 1) (hb : d146837 q = 1) : d149508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22662, d149508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22662, d149508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49985 (p : Pattern) (ha : d22668 p = 1) (hb : d146837 p = 1) : d149514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22663 q = 1) (hb : d146837 q = 1) : d149509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22663, d149509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49984 q ha hb
    | true =>
      simp only [d22663, d149509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22664 q = 1) (hb : d146837 q = 1) : d149510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22664, d149510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22664, d149510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22665 q = 1) (hb : d146837 q = 1) : d149511 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22665, d149511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22665, d149511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22666 q = 1) (hb : d146837 q = 1) : d149512 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22666, d149512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22666, d149512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22667 q = 1) (hb : d146837 q = 1) : d149513 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22667, d149513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22667, d149513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22668 q = 1) (hb : d146837 q = 1) : d149514 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22668, d149514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22668, d149514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49986 (p : Pattern) (ha : d22296 p = 1) (hb : d146837 p = 1) : d149368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49970 q ha hb
    | true =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d146837 q = 1) : d149367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22296 q = 1) (hb : d146837 q = 1) : d149368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22296, d149368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22296, d149368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49987 (p : Pattern) (ha : d22298 p = 1) (hb : d146837 p = 1) : d149370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d146837 q = 1) : d149345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d146837 q = 1) : d149369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22298 q = 1) (hb : d146837 q = 1) : d149370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22298, d149370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22298, d149370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49988 (p : Pattern) (ha : d22305 p = 1) (hb : d146837 p = 1) : d149377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49970 q ha hb
    | true =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d146837 q = 1) : d149375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d146837 q = 1) : d149376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22305 q = 1) (hb : d146837 q = 1) : d149377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22305, d149377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22305, d149377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49989 (p : Pattern) (ha : d22308 p = 1) (hb : d146837 p = 1) : d149380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d146837 q = 1) : d149378 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d146837 q = 1) : d149379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22308 q = 1) (hb : d146837 q = 1) : d149380 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22308, d149380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22308, d149380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49990 (p : Pattern) (ha : d22335 p = 1) (hb : d146837 p = 1) : d149390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22231 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22320 q = 1) (hb : d146837 q = 1) : d149385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22320, d146837, d149385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45928 q ha hb
    | true =>
      simp only [d22320, d146837, d149385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22321 q = 1) (hb : d146837 q = 1) : d149386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22321, d149386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22321, d149386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22322 q = 1) (hb : d146837 q = 1) : d149387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22322, d149387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22322, d149387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22329 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22330 q = 1) (hb : d146837 q = 1) : d149323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22330, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22330, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22331 q = 1) (hb : d146837 q = 1) : d149324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22331, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22331, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22332 q = 1) (hb : d146837 q = 1) : d149325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22332, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22332, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22333 q = 1) (hb : d146837 q = 1) : d149388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22333, d149388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22333, d149388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22239 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22240 q = 1) (hb : d146837 q = 1) : d149323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22240, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22241 q = 1) (hb : d146837 q = 1) : d149324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22242 q = 1) (hb : d146837 q = 1) : d149325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22250 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22250, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d22251 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22252 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22253 q = 1) (hb : d146837 q = 1) : d149330 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22253, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d22334 q = 1) (hb : d146837 q = 1) : d149389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22334, d149389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22334, d149389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d22335 q = 1) (hb : d146837 q = 1) : d149390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22335, d149390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d22335, d149390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro49991 (p : Pattern) (ha : d22346 p = 1) (hb : d146837 p = 1) : d149396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d146837 q = 1) : d149391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49990 q ha hb
    | true =>
      simp only [d22336, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d146837 q = 1) : d149392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49978 q ha hb
    | true =>
      simp only [d22341, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d146837 q = 1) : d149393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d146837 q = 1) : d149394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d146837 q = 1) : d149395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22346 q = 1) (hb : d146837 q = 1) : d149396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22346, d149396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22346, d149396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49992 (p : Pattern) (ha : d22427 p = 1) (hb : d146837 p = 1) : d149333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22240 q = 1) (hb : d146837 q = 1) : d149323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22240, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45902 q ha hb
    | true =>
      simp only [d22240, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d22241 q = 1) (hb : d146837 q = 1) : d149324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22241, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22241, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22242 q = 1) (hb : d146837 q = 1) : d149325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22242, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22242, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22249 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22250 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22250, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22250, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22251 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22251, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22251, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22252 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22252, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22252, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22253 q = 1) (hb : d146837 q = 1) : d149330 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22253, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22253, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22421 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d22422 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22422, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45903 q ha hb
    | true =>
      simp only [d22422, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d22423 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22423, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22423, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22424 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22424, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22424, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22425 q = 1) (hb : d146837 q = 1) : d149331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22425, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22425, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22426 q = 1) (hb : d146837 q = 1) : d149332 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22426, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22426, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22427 q = 1) (hb : d146837 q = 1) : d149333 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22427, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22427, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro49993 (p : Pattern) (ha : d22433 p = 1) (hb : d146837 p = 1) : d149402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22428 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22428, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49992 q ha hb
    | true =>
      simp only [d22428, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22429 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22429, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22429, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22430 q = 1) (hb : d146837 q = 1) : d149399 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22430, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22430, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22431 q = 1) (hb : d146837 q = 1) : d149400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22431, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22431, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22432 q = 1) (hb : d146837 q = 1) : d149401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22432, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22432, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22433 q = 1) (hb : d146837 q = 1) : d149402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22433, d149402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22433, d149402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49994 (p : Pattern) (ha : d146837 p = 1) (hb : d150201 p = 1) : d149408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22299 q = 1) (hb : d146837 q = 1) : d149371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22299, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49986 q ha hb
    | true =>
      simp only [d22299, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49987 q ha hb
  have h2 (q : Pattern) (ha : d22300 q = 1) (hb : d146837 q = 1) : d149372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22300, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22300, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22301 q = 1) (hb : d146837 q = 1) : d149373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22301, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22301, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22302 q = 1) (hb : d146837 q = 1) : d149374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22302, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22302, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22309 q = 1) (hb : d146837 q = 1) : d149381 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22309, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49988 q ha hb
    | true =>
      simp only [d22309, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49989 q ha hb
  have h6 (q : Pattern) (ha : d22310 q = 1) (hb : d146837 q = 1) : d149382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22310, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22310, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22311 q = 1) (hb : d146837 q = 1) : d149383 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22311, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22311, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22351 q = 1) (hb : d146837 q = 1) : d149397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22351, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49991 q ha hb
    | true =>
      simp only [d22351, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49979 q ha hb
  have h9 (q : Pattern) (ha : d146837 q = 1) (hb : d150197 q = 1) : d149398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150197, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d22434 q = 1) (hb : d146837 q = 1) : d149403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22434, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49993 q ha hb
    | true =>
      simp only [d22434, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22435 q = 1) (hb : d146837 q = 1) : d149404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22435, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22435, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146837 q = 1) (hb : d150198 q = 1) : d149405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150198, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146837 q = 1) (hb : d150199 q = 1) : d149406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150199, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146837 q = 1) (hb : d150200 q = 1) : d149407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150200, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146837 q = 1) (hb : d150201 q = 1) : d149408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150201, d149408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150201, d149408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49995 (p : Pattern) (ha : d22440 p = 1) (hb : d146837 p = 1) : d149409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49970 q ha hb
    | true =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22269 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22269, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22269, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22295 q = 1) (hb : d146837 q = 1) : d149367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22295, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22295, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22440 q = 1) (hb : d146837 q = 1) : d149409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22440, d149409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22440, d149409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49996 (p : Pattern) (ha : d22441 p = 1) (hb : d146837 p = 1) : d149410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22273 q = 1) (hb : d146837 q = 1) : d149345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22273, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22273, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22297 q = 1) (hb : d146837 q = 1) : d149369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22297, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22297, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22441 q = 1) (hb : d146837 q = 1) : d149410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22441, d149410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22441, d149410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49997 (p : Pattern) (ha : d22446 p = 1) (hb : d146837 p = 1) : d149415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22262 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49970 q ha hb
    | true =>
      simp only [d22262, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22263 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22263, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22268 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22268, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22303 q = 1) (hb : d146837 q = 1) : d149375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22303, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22303, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22304 q = 1) (hb : d146837 q = 1) : d149376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22304, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22304, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22446 q = 1) (hb : d146837 q = 1) : d149415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22446, d149415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22446, d149415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49998 (p : Pattern) (ha : d22447 p = 1) (hb : d146837 p = 1) : d149416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22266 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49971 q ha hb
    | true =>
      simp only [d22266, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22267 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22267, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22272 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22272, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22306 q = 1) (hb : d146837 q = 1) : d149378 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22306, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22306, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22307 q = 1) (hb : d146837 q = 1) : d149379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22307, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22307, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22447 q = 1) (hb : d146837 q = 1) : d149416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22447, d149416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22447, d149416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49999 (p : Pattern) (ha : d22451 p = 1) (hb : d146837 p = 1) : d149420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22336 q = 1) (hb : d146837 q = 1) : d149391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22336, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49990 q ha hb
    | true =>
      simp only [d22336, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22337 q = 1) (hb : d146837 q = 1) : d149392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22337, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22337, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22341 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22341, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49978 q ha hb
    | true =>
      simp only [d22341, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22342 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22342, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22342, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22343 q = 1) (hb : d146837 q = 1) : d149393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22343, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22343, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22344 q = 1) (hb : d146837 q = 1) : d149394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22344, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22344, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22345 q = 1) (hb : d146837 q = 1) : d149395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22345, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22345, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22451 q = 1) (hb : d146837 q = 1) : d149420 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22451, d149420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22451, d149420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
