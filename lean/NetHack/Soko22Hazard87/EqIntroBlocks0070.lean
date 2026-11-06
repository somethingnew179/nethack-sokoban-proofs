import NetHack.Soko22Hazard87.EqIntroBlocks0069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro17500 (p : Pattern) (selected : d188905 p = 0) : d189450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188876 q = 0) : d189434 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188876, d189434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17492 q selected
    | true =>
      simp only [d188876, d189434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17494 q selected
  have h2 (q : Pattern) (selected : d188894 q = 0) : d189439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188894, d189439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17497 q selected
    | true =>
      simp only [d188894, d189439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17498 q selected
  have h3 (q : Pattern) (selected : d188895 q = 0) : d189440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188895, d189440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188895, d189440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188900 q = 0) : d189445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188900, d189445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17499 q selected
    | true =>
      simp only [d188900, d189445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188901 q = 0) : d189446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188901, d189446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188901, d189446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188902 q = 0) : d189447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188902, d189447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188902, d189447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d188903 q = 0) : d189448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188903, d189448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188903, d189448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d188904 q = 0) : d189449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188904, d189449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188904, d189449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d188905 q = 0) : d189450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188905, d189450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188905, d189450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17501 (p : Pattern) (selected : d188910 p = 0) : d189438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188870 q = 0) : d189428 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188870, d189428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17493 q selected
    | true =>
      simp only [d188870, d189428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188871 q = 0) : d189429 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188871, d189429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188871, d189429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188907 q = 0) : d189435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188907, d189435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188907, d189435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188908 q = 0) : d189436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188908, d189436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188908, d189436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188909 q = 0) : d189437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188909, d189437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188909, d189437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188910 q = 0) : d189438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188910, d189438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188910, d189438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17502 (p : Pattern) (selected : d188916 p = 0) : d189457 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188911 q = 0) : d189452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188911, d189452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17501 q selected
    | true =>
      simp only [d188911, d189452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188912 q = 0) : d189453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188912, d189453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188912, d189453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188913 q = 0) : d189454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188913, d189454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188913, d189454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188914 q = 0) : d189455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188914, d189455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188914, d189455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188915 q = 0) : d189456 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188915, d189456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188915, d189456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188916 q = 0) : d189457 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188916, d189457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188916, d189457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17503 (p : Pattern) (selected : d188922 p = 0) : d189463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188906 q = 0) : d189451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188906, d189451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188906, d189451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17500 q selected
  have h2 (q : Pattern) (selected : d188917 q = 0) : d189458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188917, d189458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188917, d189458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17502 q selected
  have h3 (q : Pattern) (selected : d188918 q = 0) : d189459 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188918, d189459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188918, d189459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188919 q = 0) : d189460 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188919, d189460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188919, d189460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188920 q = 0) : d189461 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188920, d189461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188920, d189461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188921 q = 0) : d189462 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188921, d189462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188921, d189462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188922 q = 0) : d189463 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188922, d189463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188922, d189463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17504 (p : Pattern) (selected : d188928 p = 0) : d189469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188923 q = 0) : d189464 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188923, d189464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188923, d189464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17503 q selected
  have h2 (q : Pattern) (selected : d188924 q = 0) : d189465 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188924, d189465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188924, d189465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188925 q = 0) : d189466 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188925, d189466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188925, d189466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188926 q = 0) : d189467 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188926, d189467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188926, d189467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188927 q = 0) : d189468 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188927, d189468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188927, d189468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188928 q = 0) : d189469 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188928, d189469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188928, d189469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17505 (p : Pattern) (selected : d188936 p = 0) : d189477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9609 q = 0) : d101189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6643 q selected
    | true =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6644 q selected
  have h2 (q : Pattern) (selected : d188930 q = 0) : d189471 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188930, d189471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188930, d189471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9614 q = 0) : d101194 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6644 q selected
    | true =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6645 q selected
  have h4 (q : Pattern) (selected : d188931 q = 0) : d189472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188931, d189472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188931, d189472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188932 q = 0) : d189473 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188932, d189473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188932, d189473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9620 q = 0) : d101200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6644 q selected
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
  have h7 (q : Pattern) (selected : d188933 q = 0) : d189474 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188933, d189474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188933, d189474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9624 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6647 q selected
  have h9 (q : Pattern) (selected : d188934 q = 0) : d189475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188934, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188934, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d188935 q = 0) : d189476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188935, d189476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d188935, d189476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d188936 q = 0) : d189477 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188936, d189477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188936, d189477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17506 (p : Pattern) (selected : d188940 p = 0) : d189481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9620 q = 0) : d101200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6644 q selected
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
  have h2 (q : Pattern) (selected : d188933 q = 0) : d189474 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188933, d189474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188933, d189474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9624 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6647 q selected
  have h4 (q : Pattern) (selected : d188934 q = 0) : d189475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188934, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188934, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188935 q = 0) : d189476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188935, d189476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188935, d189476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188939 q = 0) : d189480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188939, d189480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188939, d189480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188940 q = 0) : d189481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188940, d189481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188940, d189481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17507 (p : Pattern) (selected : d188946 p = 0) : d189487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188937 q = 0) : d189478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188937, d189478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17505 q selected
    | true =>
      simp only [d188937, d189478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188938 q = 0) : d189479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188938, d189479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188938, d189479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188941 q = 0) : d189482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188941, d189482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17506 q selected
    | true =>
      simp only [d188941, d189482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188942 q = 0) : d189483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188942, d189483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188942, d189483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188943 q = 0) : d189484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188943, d189484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188943, d189484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188944 q = 0) : d189485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188944, d189485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188944, d189485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188945 q = 0) : d189486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188945, d189486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d188945, d189486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d188946 q = 0) : d189487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188946, d189487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d188946, d189487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17508 (p : Pattern) (selected : d188947 p = 0) : d189488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9624 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6647 q selected
  have h2 (q : Pattern) (selected : d188934 q = 0) : d189475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188934, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188934, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188939 q = 0) : d189480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188939, d189480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188939, d189480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188947 q = 0) : d189488 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188947, d189488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188947, d189488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17509 (p : Pattern) (selected : d188953 p = 0) : d189494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188941 q = 0) : d189482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188941, d189482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17506 q selected
    | true =>
      simp only [d188941, d189482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188942 q = 0) : d189483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188942, d189483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188942, d189483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188948 q = 0) : d189489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188948, d189489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17508 q selected
    | true =>
      simp only [d188948, d189489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188949 q = 0) : d189490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188949, d189490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188949, d189490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188950 q = 0) : d189491 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188950, d189491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188950, d189491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188951 q = 0) : d189492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188951, d189492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188951, d189492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188952 q = 0) : d189493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188952, d189493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d188952, d189493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d188953 q = 0) : d189494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188953, d189494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d188953, d189494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17510 (p : Pattern) (selected : d188959 p = 0) : d189481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9684 q = 0) : d101200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9684, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6656 q selected
    | true =>
      simp only [d9684, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6657 q selected
  have h2 (q : Pattern) (selected : d188955 q = 0) : d189474 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188955, d189474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188955, d189474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9688 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6657 q selected
    | true =>
      simp only [d9688, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6658 q selected
  have h4 (q : Pattern) (selected : d188956 q = 0) : d189475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188956, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188956, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188957 q = 0) : d189476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188957, d189476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188957, d189476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188958 q = 0) : d189480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188958, d189480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188958, d189480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188959 q = 0) : d189481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188959, d189481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188959, d189481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17511 (p : Pattern) (selected : d188962 p = 0) : d189488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9688 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6657 q selected
    | true =>
      simp only [d9688, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6658 q selected
  have h2 (q : Pattern) (selected : d188956 q = 0) : d189475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188956, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188956, d189475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188958 q = 0) : d189480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188958, d189480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188958, d189480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188962 q = 0) : d189488 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188962, d189488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188962, d189488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17512 (p : Pattern) (selected : d188968 p = 0) : d189494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188960 q = 0) : d189482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188960, d189482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17510 q selected
    | true =>
      simp only [d188960, d189482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188961 q = 0) : d189483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188961, d189483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188961, d189483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188963 q = 0) : d189489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188963, d189489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17511 q selected
    | true =>
      simp only [d188963, d189489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188964 q = 0) : d189490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188964, d189490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188964, d189490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188965 q = 0) : d189491 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188965, d189491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188965, d189491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188966 q = 0) : d189492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188966, d189492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188966, d189492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188967 q = 0) : d189493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188967, d189493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d188967, d189493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d188968 q = 0) : d189494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188968, d189494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d188968, d189494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17513 (p : Pattern) (selected : d188972 p = 0) : d189499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188963 q = 0) : d189489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188963, d189489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17511 q selected
    | true =>
      simp only [d188963, d189489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188964 q = 0) : d189490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188964, d189490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188964, d189490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188969 q = 0) : d189496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188969, d189496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188969, d189496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188970 q = 0) : d189497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188970, d189497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188970, d189497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188971 q = 0) : d189498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188971, d189498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188971, d189498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188972 q = 0) : d189499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188972, d189499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188972, d189499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17514 (p : Pattern) (selected : d188978 p = 0) : d189505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188941 q = 0) : d189482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188941, d189482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17506 q selected
    | true =>
      simp only [d188941, d189482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188942 q = 0) : d189483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188942, d189483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188942, d189483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188975 q = 0) : d189502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188975, d189502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188975, d189502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188976 q = 0) : d189503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188976, d189503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188976, d189503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188977 q = 0) : d189504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188977, d189504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188977, d189504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188978 q = 0) : d189505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188978, d189505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188978, d189505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17515 (p : Pattern) (selected : d188984 p = 0) : d189511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188954 q = 0) : d189495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188954, d189495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17507 q selected
    | true =>
      simp only [d188954, d189495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17509 q selected
  have h2 (q : Pattern) (selected : d188973 q = 0) : d189500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188973, d189500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17512 q selected
    | true =>
      simp only [d188973, d189500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17513 q selected
  have h3 (q : Pattern) (selected : d188974 q = 0) : d189501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188974, d189501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188974, d189501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188979 q = 0) : d189506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188979, d189506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17514 q selected
    | true =>
      simp only [d188979, d189506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188980 q = 0) : d189507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188980, d189507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188980, d189507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188981 q = 0) : d189508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188981, d189508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188981, d189508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d188982 q = 0) : d189509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188982, d189509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188982, d189509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d188983 q = 0) : d189510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188983, d189510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188983, d189510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d188984 q = 0) : d189511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188984, d189511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188984, d189511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17516 (p : Pattern) (selected : d188989 p = 0) : d189499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188948 q = 0) : d189489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188948, d189489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17508 q selected
    | true =>
      simp only [d188948, d189489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188949 q = 0) : d189490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188949, d189490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188949, d189490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188986 q = 0) : d189496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188986, d189496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188986, d189496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188987 q = 0) : d189497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188987, d189497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188987, d189497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188988 q = 0) : d189498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188988, d189498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188988, d189498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188989 q = 0) : d189499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188989, d189499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188989, d189499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17517 (p : Pattern) (selected : d188995 p = 0) : d189518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188990 q = 0) : d189513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188990, d189513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17516 q selected
    | true =>
      simp only [d188990, d189513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188991 q = 0) : d189514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188991, d189514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188991, d189514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188992 q = 0) : d189515 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188992, d189515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188992, d189515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188993 q = 0) : d189516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188993, d189516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188993, d189516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188994 q = 0) : d189517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188994, d189517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188994, d189517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188995 q = 0) : d189518 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188995, d189518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188995, d189518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17518 (p : Pattern) (selected : d189001 p = 0) : d189524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d188985 q = 0) : d189512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188985, d189512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188985, d189512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17515 q selected
  have h2 (q : Pattern) (selected : d188996 q = 0) : d189519 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188996, d189519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188996, d189519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17517 q selected
  have h3 (q : Pattern) (selected : d188997 q = 0) : d189520 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188997, d189520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188997, d189520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188998 q = 0) : d189521 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188998, d189521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188998, d189521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188999 q = 0) : d189522 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188999, d189522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188999, d189522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189000 q = 0) : d189523 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189000, d189523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189000, d189523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189001 q = 0) : d189524 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189001, d189524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189001, d189524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17519 (p : Pattern) (selected : d189007 p = 0) : d189530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189002 q = 0) : d189525 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189002, d189525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189002, d189525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17518 q selected
  have h2 (q : Pattern) (selected : d189003 q = 0) : d189526 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189003, d189526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189003, d189526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189004 q = 0) : d189527 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189004, d189527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189004, d189527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189005 q = 0) : d189528 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189005, d189528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189005, d189528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189006 q = 0) : d189529 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189006, d189529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189006, d189529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189007 q = 0) : d189530 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189007, d189530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189007, d189530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17520 (p : Pattern) (selected : d189016 p = 0) : d189539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9807 q = 0) : d101328 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6673 q selected
    | true =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
  have h2 (q : Pattern) (selected : d189010 q = 0) : d189533 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189010, d189533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189010, d189533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9822 q = 0) : d101343 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
    | true =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6678 q selected
  have h4 (q : Pattern) (selected : d189011 q = 0) : d189534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189011, d189534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189011, d189534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189012 q = 0) : d189535 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189012, d189535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189012, d189535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9834 q = 0) : d101355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
  have h7 (q : Pattern) (selected : d189013 q = 0) : d189536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189013, d189536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189013, d189536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9851 q = 0) : d101372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6681 q selected
  have h9 (q : Pattern) (selected : d189014 q = 0) : d189537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189014, d189537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189014, d189537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d189015 q = 0) : d189538 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189015, d189538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189015, d189538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d189016 q = 0) : d189539 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189016, d189539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189016, d189539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17521 (p : Pattern) (selected : d189020 p = 0) : d189543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9834 q = 0) : d101355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
  have h2 (q : Pattern) (selected : d189013 q = 0) : d189536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189013, d189536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189013, d189536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9851 q = 0) : d101372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6681 q selected
  have h4 (q : Pattern) (selected : d189014 q = 0) : d189537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189014, d189537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189014, d189537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189015 q = 0) : d189538 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189015, d189538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189015, d189538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189019 q = 0) : d189542 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189019, d189542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189019, d189542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189020 q = 0) : d189543 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189020, d189543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189020, d189543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17522 (p : Pattern) (selected : d189026 p = 0) : d189549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189017 q = 0) : d189540 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189017, d189540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17520 q selected
    | true =>
      simp only [d189017, d189540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189018 q = 0) : d189541 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189018, d189541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189018, d189541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189021 q = 0) : d189544 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189021, d189544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17521 q selected
    | true =>
      simp only [d189021, d189544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189022 q = 0) : d189545 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189022, d189545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189022, d189545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189023 q = 0) : d189546 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189023, d189546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189023, d189546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189024 q = 0) : d189547 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189024, d189547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189024, d189547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189025 q = 0) : d189548 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189025, d189548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189025, d189548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189026 q = 0) : d189549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189026, d189549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189026, d189549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17523 (p : Pattern) (selected : d189029 p = 0) : d189552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9870 q = 0) : d101391 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6685 q selected
  have h2 (q : Pattern) (selected : d189027 q = 0) : d189550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189027, d189550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189027, d189550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189028 q = 0) : d189551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189028, d189551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189028, d189551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189029 q = 0) : d189552 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189029, d189552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189029, d189552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17524 (p : Pattern) (selected : d189035 p = 0) : d189558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189021 q = 0) : d189544 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189021, d189544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17521 q selected
    | true =>
      simp only [d189021, d189544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189022 q = 0) : d189545 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189022, d189545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189022, d189545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189030 q = 0) : d189553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189030, d189553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17523 q selected
    | true =>
      simp only [d189030, d189553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189031 q = 0) : d189554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189031, d189554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189031, d189554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189032 q = 0) : d189555 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189032, d189555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189032, d189555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189033 q = 0) : d189556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189033, d189556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189033, d189556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189034 q = 0) : d189557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189034, d189557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189034, d189557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189035 q = 0) : d189558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189035, d189558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189035, d189558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17525 (p : Pattern) (selected : d189042 p = 0) : d189560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9934 q = 0) : d101355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9934, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6693 q selected
    | true =>
      simp only [d9934, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6694 q selected
  have h2 (q : Pattern) (selected : d189037 q = 0) : d189536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189037, d189536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189037, d189536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9959 q = 0) : d101372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9959, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6694 q selected
    | true =>
      simp only [d9959, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6697 q selected
  have h4 (q : Pattern) (selected : d189038 q = 0) : d189537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189038, d189537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189038, d189537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189039 q = 0) : d189538 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189039, d189538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189039, d189538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9965 q = 0) : d101391 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6694 q selected
    | true =>
      simp only [d9965, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6698 q selected
  have h7 (q : Pattern) (selected : d189040 q = 0) : d189550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189040, d189550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189040, d189550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189041 q = 0) : d189551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189041, d189551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189041, d189551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189042 q = 0) : d189560 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189042, d189560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189042, d189560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17526 (p : Pattern) (selected : d189045 p = 0) : d189552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9965 q = 0) : d101391 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6694 q selected
    | true =>
      simp only [d9965, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6698 q selected
  have h2 (q : Pattern) (selected : d189040 q = 0) : d189550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189040, d189550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189040, d189550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189041 q = 0) : d189551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189041, d189551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189041, d189551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189045 q = 0) : d189552 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189045, d189552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189045, d189552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17527 (p : Pattern) (selected : d189051 p = 0) : d189566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189043 q = 0) : d189561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189043, d189561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17525 q selected
    | true =>
      simp only [d189043, d189561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189044 q = 0) : d189562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189044, d189562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189044, d189562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189046 q = 0) : d189553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189046, d189553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17526 q selected
    | true =>
      simp only [d189046, d189553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189047 q = 0) : d189554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189047, d189554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189047, d189554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189048 q = 0) : d189563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189048, d189563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189048, d189563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189049 q = 0) : d189564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189049, d189564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189049, d189564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189050 q = 0) : d189565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189050, d189565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189050, d189565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189051 q = 0) : d189566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189051, d189566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189051, d189566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17528 (p : Pattern) (selected : d189055 p = 0) : d189570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189046 q = 0) : d189553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189046, d189553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17526 q selected
    | true =>
      simp only [d189046, d189553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189047 q = 0) : d189554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189047, d189554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189047, d189554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189052 q = 0) : d189567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189052, d189567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189052, d189567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189053 q = 0) : d189568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189053, d189568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189053, d189568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189054 q = 0) : d189569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189054, d189569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189054, d189569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189055 q = 0) : d189570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189055, d189570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189055, d189570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17529 (p : Pattern) (selected : d189060 p = 0) : d189575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9834 q = 0) : d101355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
  have h2 (q : Pattern) (selected : d189013 q = 0) : d189536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189013, d189536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189013, d189536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9851 q = 0) : d101372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6681 q selected
  have h4 (q : Pattern) (selected : d189014 q = 0) : d189537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189014, d189537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189014, d189537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189015 q = 0) : d189538 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189015, d189538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189015, d189538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9988 q = 0) : d101419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6703 q selected
  have h7 (q : Pattern) (selected : d189058 q = 0) : d189573 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189058, d189573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189058, d189573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189059 q = 0) : d189574 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189059, d189574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189059, d189574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189060 q = 0) : d189575 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189060, d189575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189060, d189575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17530 (p : Pattern) (selected : d189066 p = 0) : d189581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189061 q = 0) : d189576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189061, d189576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17529 q selected
    | true =>
      simp only [d189061, d189576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189062 q = 0) : d189577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189062, d189577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189062, d189577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189063 q = 0) : d189578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189063, d189578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189063, d189578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189064 q = 0) : d189579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189064, d189579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189064, d189579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189065 q = 0) : d189580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189065, d189580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189065, d189580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189066 q = 0) : d189581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189066, d189581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189066, d189581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17531 (p : Pattern) (selected : d189072 p = 0) : d189587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189036 q = 0) : d189559 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189036, d189559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17522 q selected
    | true =>
      simp only [d189036, d189559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17524 q selected
  have h2 (q : Pattern) (selected : d189056 q = 0) : d189571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189056, d189571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17527 q selected
    | true =>
      simp only [d189056, d189571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17528 q selected
  have h3 (q : Pattern) (selected : d189057 q = 0) : d189572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189057, d189572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189057, d189572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189067 q = 0) : d189582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189067, d189582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17530 q selected
    | true =>
      simp only [d189067, d189582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189068 q = 0) : d189583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189068, d189583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189068, d189583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189069 q = 0) : d189584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189069, d189584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189069, d189584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d189070 q = 0) : d189585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189070, d189585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189070, d189585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189071 q = 0) : d189586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189071, d189586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189071, d189586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d189072 q = 0) : d189587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189072, d189587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189072, d189587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17532 (p : Pattern) (selected : d189077 p = 0) : d189570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189030 q = 0) : d189553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189030, d189553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17523 q selected
    | true =>
      simp only [d189030, d189553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189031 q = 0) : d189554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189031, d189554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189031, d189554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189074 q = 0) : d189567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189074, d189567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189074, d189567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189075 q = 0) : d189568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189075, d189568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189075, d189568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189076 q = 0) : d189569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189076, d189569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189076, d189569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189077 q = 0) : d189570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189077, d189570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189077, d189570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17533 (p : Pattern) (selected : d189083 p = 0) : d189594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189078 q = 0) : d189589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189078, d189589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17532 q selected
    | true =>
      simp only [d189078, d189589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189079 q = 0) : d189590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189079, d189590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189079, d189590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189080 q = 0) : d189591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189080, d189591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189080, d189591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189081 q = 0) : d189592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189081, d189592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189081, d189592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189082 q = 0) : d189593 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189082, d189593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189082, d189593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189083 q = 0) : d189594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189083, d189594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189083, d189594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17534 (p : Pattern) (selected : d189089 p = 0) : d189600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189073 q = 0) : d189588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189073, d189588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189073, d189588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17531 q selected
  have h2 (q : Pattern) (selected : d189084 q = 0) : d189595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189084, d189595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189084, d189595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17533 q selected
  have h3 (q : Pattern) (selected : d189085 q = 0) : d189596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189085, d189596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189085, d189596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189086 q = 0) : d189597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189086, d189597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189086, d189597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189087 q = 0) : d189598 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189087, d189598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189087, d189598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189088 q = 0) : d189599 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189088, d189599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189088, d189599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189089 q = 0) : d189600 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189089, d189600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189089, d189600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17535 (p : Pattern) (selected : d189095 p = 0) : d189606 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189090 q = 0) : d189601 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189090, d189601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189090, d189601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17534 q selected
  have h2 (q : Pattern) (selected : d189091 q = 0) : d189602 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189091, d189602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189091, d189602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189092 q = 0) : d189603 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189092, d189603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189092, d189603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189093 q = 0) : d189604 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189093, d189604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189093, d189604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189094 q = 0) : d189605 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189094, d189605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189094, d189605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189095 q = 0) : d189606 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189095, d189606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189095, d189606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17536 (p : Pattern) (selected : d189105 p = 0) : d189616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10092 q = 0) : d101519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6715 q selected
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
  have h2 (q : Pattern) (selected : d189099 q = 0) : d189610 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189099, d189610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189099, d189610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10107 q = 0) : d101534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6720 q selected
  have h4 (q : Pattern) (selected : d189100 q = 0) : d189611 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189100, d189611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189100, d189611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189101 q = 0) : d189612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189101, d189612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189101, d189612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h7 (q : Pattern) (selected : d189102 q = 0) : d189613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189102, d189613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189102, d189613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h9 (q : Pattern) (selected : d189103 q = 0) : d189614 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189103, d189614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189103, d189614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d189104 q = 0) : d189615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189104, d189615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189104, d189615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d189105 q = 0) : d189616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189105, d189616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189105, d189616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17537 (p : Pattern) (selected : d189109 p = 0) : d189620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h2 (q : Pattern) (selected : d189102 q = 0) : d189613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189102, d189613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189102, d189613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h4 (q : Pattern) (selected : d189103 q = 0) : d189614 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189103, d189614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189103, d189614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189104 q = 0) : d189615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189104, d189615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189104, d189615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189108 q = 0) : d189619 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189108, d189619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189108, d189619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189109 q = 0) : d189620 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189109, d189620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189109, d189620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17538 (p : Pattern) (selected : d189115 p = 0) : d189626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189106 q = 0) : d189617 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189106, d189617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17536 q selected
    | true =>
      simp only [d189106, d189617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189107 q = 0) : d189618 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189107, d189618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189107, d189618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189110 q = 0) : d189621 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189110, d189621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17537 q selected
    | true =>
      simp only [d189110, d189621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189111 q = 0) : d189622 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189111, d189622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189111, d189622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189112 q = 0) : d189623 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189112, d189623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189112, d189623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189113 q = 0) : d189624 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189113, d189624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189113, d189624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189114 q = 0) : d189625 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189114, d189625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189114, d189625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189115 q = 0) : d189626 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189115, d189626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189115, d189626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17539 (p : Pattern) (selected : d189118 p = 0) : d189629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10164 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6728 q selected
  have h2 (q : Pattern) (selected : d189116 q = 0) : d189627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189116, d189627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189116, d189627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189117 q = 0) : d189628 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189117, d189628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189117, d189628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189118 q = 0) : d189629 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189118, d189629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189118, d189629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17540 (p : Pattern) (selected : d189124 p = 0) : d189635 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189110 q = 0) : d189621 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189110, d189621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17537 q selected
    | true =>
      simp only [d189110, d189621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189111 q = 0) : d189622 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189111, d189622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189111, d189622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189119 q = 0) : d189630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189119, d189630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17539 q selected
    | true =>
      simp only [d189119, d189630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189120 q = 0) : d189631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189120, d189631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189120, d189631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189121 q = 0) : d189632 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189121, d189632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189121, d189632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189122 q = 0) : d189633 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189122, d189633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189122, d189633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189123 q = 0) : d189634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189123, d189634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189123, d189634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189124 q = 0) : d189635 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189124, d189635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189124, d189635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17541 (p : Pattern) (selected : d189131 p = 0) : d189637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10234 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10234, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6736 q selected
    | true =>
      simp only [d10234, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
  have h2 (q : Pattern) (selected : d189126 q = 0) : d189613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189126, d189613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189126, d189613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10262 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10262, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10262, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6741 q selected
  have h4 (q : Pattern) (selected : d189127 q = 0) : d189614 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189127, d189614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189127, d189614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189128 q = 0) : d189615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189128, d189615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189128, d189615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10271 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6742 q selected
  have h7 (q : Pattern) (selected : d189129 q = 0) : d189627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189129, d189627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189129, d189627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189130 q = 0) : d189628 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189130, d189628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189130, d189628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189131 q = 0) : d189637 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189131, d189637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189131, d189637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17542 (p : Pattern) (selected : d189134 p = 0) : d189629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10271 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6742 q selected
  have h2 (q : Pattern) (selected : d189129 q = 0) : d189627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189129, d189627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189129, d189627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189130 q = 0) : d189628 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189130, d189628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189130, d189628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189134 q = 0) : d189629 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189134, d189629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189134, d189629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17543 (p : Pattern) (selected : d189140 p = 0) : d189643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189132 q = 0) : d189638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189132, d189638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17541 q selected
    | true =>
      simp only [d189132, d189638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189133 q = 0) : d189639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189133, d189639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189133, d189639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189135 q = 0) : d189630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189135, d189630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17542 q selected
    | true =>
      simp only [d189135, d189630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189136 q = 0) : d189631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189136, d189631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189136, d189631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189137 q = 0) : d189640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189137, d189640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189137, d189640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189138 q = 0) : d189641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189138, d189641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189138, d189641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189139 q = 0) : d189642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189139, d189642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189139, d189642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189140 q = 0) : d189643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189140, d189643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189140, d189643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17544 (p : Pattern) (selected : d189144 p = 0) : d189647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189135 q = 0) : d189630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189135, d189630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17542 q selected
    | true =>
      simp only [d189135, d189630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189136 q = 0) : d189631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189136, d189631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189136, d189631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189141 q = 0) : d189644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189141, d189644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189141, d189644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189142 q = 0) : d189645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189142, d189645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189142, d189645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189143 q = 0) : d189646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189143, d189646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189143, d189646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189144 q = 0) : d189647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189144, d189647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189144, d189647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17545 (p : Pattern) (selected : d189149 p = 0) : d189652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h2 (q : Pattern) (selected : d189102 q = 0) : d189613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189102, d189613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189102, d189613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h4 (q : Pattern) (selected : d189103 q = 0) : d189614 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189103, d189614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189103, d189614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189104 q = 0) : d189615 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189104, d189615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189104, d189615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10294 q = 0) : d101619 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6747 q selected
  have h7 (q : Pattern) (selected : d189147 q = 0) : d189650 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189147, d189650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189147, d189650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189148 q = 0) : d189651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189148, d189651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189148, d189651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189149 q = 0) : d189652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189149, d189652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189149, d189652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17546 (p : Pattern) (selected : d189155 p = 0) : d189658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189150 q = 0) : d189653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189150, d189653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17545 q selected
    | true =>
      simp only [d189150, d189653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189151 q = 0) : d189654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189151, d189654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189151, d189654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189152 q = 0) : d189655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189152, d189655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189152, d189655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189153 q = 0) : d189656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189153, d189656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189153, d189656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189154 q = 0) : d189657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189154, d189657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189154, d189657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189155 q = 0) : d189658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189155, d189658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189155, d189658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17547 (p : Pattern) (selected : d189161 p = 0) : d189664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189125 q = 0) : d189636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189125, d189636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17538 q selected
    | true =>
      simp only [d189125, d189636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17540 q selected
  have h2 (q : Pattern) (selected : d189145 q = 0) : d189648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189145, d189648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17543 q selected
    | true =>
      simp only [d189145, d189648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17544 q selected
  have h3 (q : Pattern) (selected : d189146 q = 0) : d189649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189146, d189649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189146, d189649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189156 q = 0) : d189659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189156, d189659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17546 q selected
    | true =>
      simp only [d189156, d189659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189157 q = 0) : d189660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189157, d189660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189157, d189660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189158 q = 0) : d189661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189158, d189661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189158, d189661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d189159 q = 0) : d189662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189159, d189662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189159, d189662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189160 q = 0) : d189663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189160, d189663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189160, d189663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d189161 q = 0) : d189664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189161, d189664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189161, d189664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17548 (p : Pattern) (selected : d189166 p = 0) : d189647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189119 q = 0) : d189630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189119, d189630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17539 q selected
    | true =>
      simp only [d189119, d189630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189120 q = 0) : d189631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189120, d189631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189120, d189631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189163 q = 0) : d189644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189163, d189644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189163, d189644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189164 q = 0) : d189645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189164, d189645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189164, d189645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189165 q = 0) : d189646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189165, d189646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189165, d189646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189166 q = 0) : d189647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189166, d189647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189166, d189647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17549 (p : Pattern) (selected : d189172 p = 0) : d189671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189167 q = 0) : d189666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189167, d189666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17548 q selected
    | true =>
      simp only [d189167, d189666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189168 q = 0) : d189667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189168, d189667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189168, d189667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189169 q = 0) : d189668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189169, d189668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189169, d189668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189170 q = 0) : d189669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189170, d189669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189170, d189669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189171 q = 0) : d189670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189171, d189670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189171, d189670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189172 q = 0) : d189671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189172, d189671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189172, d189671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17550 (p : Pattern) (selected : d189178 p = 0) : d189677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189162 q = 0) : d189665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189162, d189665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189162, d189665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17547 q selected
  have h2 (q : Pattern) (selected : d189173 q = 0) : d189672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189173, d189672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189173, d189672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17549 q selected
  have h3 (q : Pattern) (selected : d189174 q = 0) : d189673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189174, d189673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189174, d189673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189175 q = 0) : d189674 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189175, d189674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189175, d189674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189176 q = 0) : d189675 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189176, d189675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189176, d189675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189177 q = 0) : d189676 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189177, d189676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189177, d189676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189178 q = 0) : d189677 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189178, d189677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189178, d189677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17551 (p : Pattern) (selected : d189184 p = 0) : d189683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189179 q = 0) : d189678 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189179, d189678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189179, d189678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17550 q selected
  have h2 (q : Pattern) (selected : d189180 q = 0) : d189679 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189180, d189679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189180, d189679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189181 q = 0) : d189680 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189181, d189680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189181, d189680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189182 q = 0) : d189681 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189182, d189681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189182, d189681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189183 q = 0) : d189682 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189183, d189682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189183, d189682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189184 q = 0) : d189683 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189184, d189683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189184, d189683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17552 (p : Pattern) (selected : d189195 p = 0) : d189694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10378 q = 0) : d101699 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6757 q selected
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
  have h2 (q : Pattern) (selected : d189189 q = 0) : d189688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189189, d189688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189189, d189688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10383 q = 0) : d101704 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6761 q selected
  have h4 (q : Pattern) (selected : d189190 q = 0) : d189689 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189190, d189689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189190, d189689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189191 q = 0) : d189690 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189191, d189690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189191, d189690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h7 (q : Pattern) (selected : d189192 q = 0) : d189691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189192, d189691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189192, d189691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h9 (q : Pattern) (selected : d189193 q = 0) : d189692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189193, d189692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189193, d189692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d189194 q = 0) : d189693 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189194, d189693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189194, d189693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d189195 q = 0) : d189694 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189195, d189694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189195, d189694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17553 (p : Pattern) (selected : d189199 p = 0) : d189698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h2 (q : Pattern) (selected : d189192 q = 0) : d189691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189192, d189691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189192, d189691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h4 (q : Pattern) (selected : d189193 q = 0) : d189692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189193, d189692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189193, d189692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189194 q = 0) : d189693 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189194, d189693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189194, d189693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189198 q = 0) : d189697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189198, d189697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189198, d189697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189199 q = 0) : d189698 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189199, d189698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189199, d189698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17554 (p : Pattern) (selected : d189205 p = 0) : d189704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189196 q = 0) : d189695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189196, d189695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17552 q selected
    | true =>
      simp only [d189196, d189695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189197 q = 0) : d189696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189197, d189696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189197, d189696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189200 q = 0) : d189699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189200, d189699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17553 q selected
    | true =>
      simp only [d189200, d189699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189201 q = 0) : d189700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189201, d189700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189201, d189700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189202 q = 0) : d189701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189202, d189701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189202, d189701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189203 q = 0) : d189702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189203, d189702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189203, d189702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189204 q = 0) : d189703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189204, d189703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189204, d189703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189205 q = 0) : d189704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189205, d189704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189205, d189704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17555 (p : Pattern) (selected : d189208 p = 0) : d189707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10441 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6769 q selected
  have h2 (q : Pattern) (selected : d189206 q = 0) : d189705 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189206, d189705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189206, d189705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189207 q = 0) : d189706 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189207, d189706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189207, d189706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189208 q = 0) : d189707 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189208, d189707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189208, d189707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17556 (p : Pattern) (selected : d189214 p = 0) : d189713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189200 q = 0) : d189699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189200, d189699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17553 q selected
    | true =>
      simp only [d189200, d189699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189201 q = 0) : d189700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189201, d189700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189201, d189700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189209 q = 0) : d189708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189209, d189708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17555 q selected
    | true =>
      simp only [d189209, d189708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189210 q = 0) : d189709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189210, d189709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189210, d189709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189211 q = 0) : d189710 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189211, d189710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189211, d189710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189212 q = 0) : d189711 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189212, d189711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189212, d189711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189213 q = 0) : d189712 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189213, d189712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189213, d189712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189214 q = 0) : d189713 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189214, d189713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189214, d189713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17557 (p : Pattern) (selected : d189221 p = 0) : d189715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10501 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10501, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6775 q selected
    | true =>
      simp only [d10501, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
  have h2 (q : Pattern) (selected : d189216 q = 0) : d189691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189216, d189691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189216, d189691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10528 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10528, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10528, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6780 q selected
  have h4 (q : Pattern) (selected : d189217 q = 0) : d189692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189217, d189692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189217, d189692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189218 q = 0) : d189693 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189218, d189693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189218, d189693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10537 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6781 q selected
  have h7 (q : Pattern) (selected : d189219 q = 0) : d189705 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189219, d189705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189219, d189705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189220 q = 0) : d189706 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189220, d189706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189220, d189706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189221 q = 0) : d189715 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189221, d189715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189221, d189715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17558 (p : Pattern) (selected : d189224 p = 0) : d189707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10537 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6781 q selected
  have h2 (q : Pattern) (selected : d189219 q = 0) : d189705 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189219, d189705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189219, d189705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189220 q = 0) : d189706 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189220, d189706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189220, d189706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189224 q = 0) : d189707 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189224, d189707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189224, d189707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17559 (p : Pattern) (selected : d189230 p = 0) : d189721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189222 q = 0) : d189716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189222, d189716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17557 q selected
    | true =>
      simp only [d189222, d189716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189223 q = 0) : d189717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189223, d189717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189223, d189717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189225 q = 0) : d189708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189225, d189708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17558 q selected
    | true =>
      simp only [d189225, d189708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189226 q = 0) : d189709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189226, d189709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189226, d189709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189227 q = 0) : d189718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189227, d189718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189227, d189718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189228 q = 0) : d189719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189228, d189719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189228, d189719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189229 q = 0) : d189720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189229, d189720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189229, d189720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189230 q = 0) : d189721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189230, d189721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189230, d189721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17560 (p : Pattern) (selected : d189234 p = 0) : d189725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189225 q = 0) : d189708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189225, d189708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17558 q selected
    | true =>
      simp only [d189225, d189708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189226 q = 0) : d189709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189226, d189709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189226, d189709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189231 q = 0) : d189722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189231, d189722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189231, d189722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189232 q = 0) : d189723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189232, d189723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189232, d189723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189233 q = 0) : d189724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189233, d189724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189233, d189724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189234 q = 0) : d189725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189234, d189725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189234, d189725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17561 (p : Pattern) (selected : d189239 p = 0) : d189730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h2 (q : Pattern) (selected : d189192 q = 0) : d189691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189192, d189691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189192, d189691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h4 (q : Pattern) (selected : d189193 q = 0) : d189692 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189193, d189692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189193, d189692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189194 q = 0) : d189693 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189194, d189693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189194, d189693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10560 q = 0) : d101790 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6786 q selected
  have h7 (q : Pattern) (selected : d189237 q = 0) : d189728 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189237, d189728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189237, d189728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189238 q = 0) : d189729 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189238, d189729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189238, d189729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189239 q = 0) : d189730 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189239, d189730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189239, d189730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17562 (p : Pattern) (selected : d189245 p = 0) : d189736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189240 q = 0) : d189731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189240, d189731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17561 q selected
    | true =>
      simp only [d189240, d189731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189241 q = 0) : d189732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189241, d189732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189241, d189732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189242 q = 0) : d189733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189242, d189733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189242, d189733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189243 q = 0) : d189734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189243, d189734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189243, d189734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189244 q = 0) : d189735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189244, d189735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189244, d189735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189245 q = 0) : d189736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189245, d189736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189245, d189736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17563 (p : Pattern) (selected : d189251 p = 0) : d189742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189215 q = 0) : d189714 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189215, d189714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17554 q selected
    | true =>
      simp only [d189215, d189714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17556 q selected
  have h2 (q : Pattern) (selected : d189235 q = 0) : d189726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189235, d189726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17559 q selected
    | true =>
      simp only [d189235, d189726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17560 q selected
  have h3 (q : Pattern) (selected : d189236 q = 0) : d189727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189236, d189727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189236, d189727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189246 q = 0) : d189737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189246, d189737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17562 q selected
    | true =>
      simp only [d189246, d189737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189247 q = 0) : d189738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189247, d189738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189247, d189738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189248 q = 0) : d189739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189248, d189739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189248, d189739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d189249 q = 0) : d189740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189249, d189740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189249, d189740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189250 q = 0) : d189741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189250, d189741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189250, d189741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d189251 q = 0) : d189742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189251, d189742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189251, d189742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17564 (p : Pattern) (selected : d189256 p = 0) : d189725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189209 q = 0) : d189708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189209, d189708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17555 q selected
    | true =>
      simp only [d189209, d189708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189210 q = 0) : d189709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189210, d189709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189210, d189709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189253 q = 0) : d189722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189253, d189722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189253, d189722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189254 q = 0) : d189723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189254, d189723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189254, d189723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189255 q = 0) : d189724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189255, d189724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189255, d189724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189256 q = 0) : d189725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189256, d189725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189256, d189725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17565 (p : Pattern) (selected : d189262 p = 0) : d189749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189257 q = 0) : d189744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189257, d189744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17564 q selected
    | true =>
      simp only [d189257, d189744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189258 q = 0) : d189745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189258, d189745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189258, d189745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189259 q = 0) : d189746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189259, d189746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189259, d189746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189260 q = 0) : d189747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189260, d189747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189260, d189747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189261 q = 0) : d189748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189261, d189748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189261, d189748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189262 q = 0) : d189749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189262, d189749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189262, d189749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17566 (p : Pattern) (selected : d189268 p = 0) : d189755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189252 q = 0) : d189743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189252, d189743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189252, d189743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17563 q selected
  have h2 (q : Pattern) (selected : d189263 q = 0) : d189750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189263, d189750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189263, d189750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17565 q selected
  have h3 (q : Pattern) (selected : d189264 q = 0) : d189751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189264, d189751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189264, d189751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189265 q = 0) : d189752 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189265, d189752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189265, d189752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189266 q = 0) : d189753 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189266, d189753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189266, d189753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189267 q = 0) : d189754 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189267, d189754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189267, d189754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189268 q = 0) : d189755 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189268, d189755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189268, d189755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17567 (p : Pattern) (selected : d189274 p = 0) : d189761 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189269 q = 0) : d189756 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189269, d189756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189269, d189756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17566 q selected
  have h2 (q : Pattern) (selected : d189270 q = 0) : d189757 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189270, d189757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189270, d189757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189271 q = 0) : d189758 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189271, d189758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189271, d189758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189272 q = 0) : d189759 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189272, d189759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189272, d189759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189273 q = 0) : d189760 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189273, d189760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189273, d189760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189274 q = 0) : d189761 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189274, d189761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189274, d189761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17568 (p : Pattern) (selected : d189280 p = 0) : d189767 p = 1 := by
  have h0 (q : Pattern) (selected : d188929 q = 0) : d189470 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188929, d189470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17489 q selected
    | true =>
      simp only [d188929, d189470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17504 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d189008 q = 0) : d189531 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189008, d189531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189008, d189531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17519 q selected
  have h3 (q : Pattern) (selected : d189009 q = 0) : d189532 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189009, d189532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189009, d189532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189096 q = 0) : d189607 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189096, d189607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189096, d189607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17535 q selected
  have h5 (q : Pattern) (selected : d189097 q = 0) : d189608 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189097, d189608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189097, d189608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189098 q = 0) : d189609 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189098, d189609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189098, d189609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d189185 q = 0) : d189684 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189185, d189684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189185, d189684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17551 q selected
  have h8 (q : Pattern) (selected : d189186 q = 0) : d189685 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189186, d189685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189186, d189685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d189187 q = 0) : d189686 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189187, d189686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189187, d189686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d189188 q = 0) : d189687 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d189188, d189687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189188, d189687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d189275 q = 0) : d189762 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189275, d189762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189275, d189762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17567 q selected
  have h12 (q : Pattern) (selected : d189276 q = 0) : d189763 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189276, d189763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189276, d189763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d189277 q = 0) : d189764 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189277, d189764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189277, d189764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d189278 q = 0) : d189765 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d189278, d189765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189278, d189765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d189279 q = 0) : d189766 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d189279, d189766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d189279, d189766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d189280 q = 0) : d189767 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d189280, d189767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d189280, d189767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro17569 (p : Pattern) (selected : d189286 p = 0) : d189773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189281 q = 0) : d189768 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d189281, d189768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17568 q selected
    | true =>
      simp only [d189281, d189768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189282 q = 0) : d189769 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d189282, d189769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189282, d189769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189283 q = 0) : d189770 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d189283, d189770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189283, d189770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189284 q = 0) : d189771 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d189284, d189771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189284, d189771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189285 q = 0) : d189772 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d189285, d189772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189285, d189772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189286 q = 0) : d189773 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d189286, d189773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189286, d189773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17570 (p : Pattern) (selected : d189292 p = 0) : d189779 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189287 q = 0) : d189774 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d189287, d189774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17569 q selected
    | true =>
      simp only [d189287, d189774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189288 q = 0) : d189775 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d189288, d189775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189288, d189775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189289 q = 0) : d189776 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d189289, d189776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189289, d189776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189290 q = 0) : d189777 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d189290, d189777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189290, d189777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189291 q = 0) : d189778 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d189291, d189778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189291, d189778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189292 q = 0) : d189779 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d189292, d189779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189292, d189779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17571 (p : Pattern) (selected : d189298 p = 0) : d189785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189293 q = 0) : d189780 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d189293, d189780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17570 q selected
    | true =>
      simp only [d189293, d189780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189294 q = 0) : d189781 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d189294, d189781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189294, d189781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189295 q = 0) : d189782 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d189295, d189782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189295, d189782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189296 q = 0) : d189783 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d189296, d189783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189296, d189783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189297 q = 0) : d189784 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d189297, d189784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189297, d189784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189298 q = 0) : d189785 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d189298, d189785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189298, d189785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17572 (p : Pattern) (selected : d189304 p = 0) : d189791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189299 q = 0) : d189786 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d189299, d189786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17571 q selected
    | true =>
      simp only [d189299, d189786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189300 q = 0) : d189787 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d189300, d189787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189300, d189787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189301 q = 0) : d189788 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d189301, d189788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189301, d189788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189302 q = 0) : d189789 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d189302, d189789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189302, d189789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189303 q = 0) : d189790 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d189303, d189790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189303, d189790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189304 q = 0) : d189791 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d189304, d189791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189304, d189791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17573 (p : Pattern) (selected : d189310 p = 0) : d189797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189305 q = 0) : d189792 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d189305, d189792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17572 q selected
    | true =>
      simp only [d189305, d189792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189306 q = 0) : d189793 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d189306, d189793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189306, d189793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189307 q = 0) : d189794 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d189307, d189794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189307, d189794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189308 q = 0) : d189795 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d189308, d189795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189308, d189795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189309 q = 0) : d189796 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d189309, d189796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189309, d189796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189310 q = 0) : d189797 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d189310, d189797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189310, d189797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17574 (p : Pattern) (selected : d189316 p = 0) : d189803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189311 q = 0) : d189798 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d189311, d189798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17573 q selected
    | true =>
      simp only [d189311, d189798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189312 q = 0) : d189799 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d189312, d189799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189312, d189799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189313 q = 0) : d189800 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d189313, d189800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189313, d189800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189314 q = 0) : d189801 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d189314, d189801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189314, d189801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189315 q = 0) : d189802 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d189315, d189802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189315, d189802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189316 q = 0) : d189803 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d189316, d189803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189316, d189803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17575 (p : Pattern) (selected : d189322 p = 0) : d189809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d189317 q = 0) : d189804 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d189317, d189804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17574 q selected
    | true =>
      simp only [d189317, d189804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189318 q = 0) : d189805 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d189318, d189805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189318, d189805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189319 q = 0) : d189806 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d189319, d189806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189319, d189806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189320 q = 0) : d189807 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d189320, d189807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189320, d189807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189321 q = 0) : d189808 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d189321, d189808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189321, d189808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189322 q = 0) : d189809 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d189322, d189809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189322, d189809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17576 (p : Pattern) (selected : d188782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
    | true =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188780 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188781 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188782 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17577 (p : Pattern) (selected : d188788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188783 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17576 q selected
    | true =>
      simp only [d188783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188784 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188785 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188786 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188787 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188788 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17578 (p : Pattern) (selected : d188794 p = 1) : d190421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188779 q = 1) : d188779 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d188789 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17577 q selected
    | true =>
      simp only [d188789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d188790 q = 1) : d190417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188790, d190417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188790, d190417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188755 q = 1) : d188755 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d188791 q = 1) : d190418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188791, d190418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188791, d190418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188792 q = 1) : d190419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188792, d190419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188792, d190419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d188793 q = 1) : d190420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188793, d190420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188793, d190420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d188794 q = 1) : d190421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188794, d190421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188794, d190421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17579 (p : Pattern) (selected : d188800 p = 1) : d190427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188795 q = 1) : d190422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188795, d190422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188795, d190422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17578 q selected
  have h2 (q : Pattern) (selected : d188796 q = 1) : d190423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188796, d190423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188796, d190423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d188797 q = 1) : d190424 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188797, d190424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188797, d190424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188798 q = 1) : d190425 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188798, d190425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188798, d190425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188799 q = 1) : d190426 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188799, d190426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188799, d190426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188800 q = 1) : d190427 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188800, d190427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188800, d190427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17580 (p : Pattern) (selected : d188818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h2 (q : Pattern) (selected : d188816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
    | true =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188780 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188817 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188781 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188818 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17581 (p : Pattern) (selected : d188824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188819 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17580 q selected
    | true =>
      simp only [d188819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188820 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188783 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17576 q selected
    | true =>
      simp only [d188783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188784 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188821 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188822 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d188823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d188824 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d188824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17582 (p : Pattern) (selected : d188836 p = 1) : d190437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188815 q = 1) : d188815 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d188825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17581 q selected
    | true =>
      simp only [d188825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17577 q selected
  have h3 (q : Pattern) (selected : d188826 q = 1) : d190433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188826, d190433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188826, d190433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188832 q = 1) : d188832 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d188833 q = 1) : d190434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188833, d190434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188833, d190434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188834 q = 1) : d190435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188834, d190435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188834, d190435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d188835 q = 1) : d190436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188835, d190436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188835, d190436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d188836 q = 1) : d190437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188836, d190437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188836, d190437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17583 (p : Pattern) (selected : d188848 p = 1) : d190443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188837 q = 1) : d190438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188837, d190438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188837, d190438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17582 q selected
  have h2 (q : Pattern) (selected : d188843 q = 1) : d188843 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d188844 q = 1) : d190439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188844, d190439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188844, d190439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188845 q = 1) : d190440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188845, d190440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188845, d190440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188846 q = 1) : d190441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188846, d190441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188846, d190441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188847 q = 1) : d190442 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188847, d190442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188847, d190442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188848 q = 1) : d190443 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188848, d190443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188848, d190443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17584 (p : Pattern) (selected : d188854 p = 1) : d190449 p = 1 := by
  have h0 (q : Pattern) (selected : d188769 q = 1) : d188769 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d188801 q = 1) : d190428 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188801, d190428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188801, d190428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17579 q selected
  have h3 (q : Pattern) (selected : d188802 q = 1) : d190429 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188802, d190429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188802, d190429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188803 q = 1) : d190430 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188803, d190430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188803, d190430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188804 q = 1) : d190431 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188804, d190431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188804, d190431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188805 q = 1) : d190432 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188805, d190432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188805, d190432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d188849 q = 1) : d190444 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188849, d190444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188849, d190444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17583 q selected
  have h8 (q : Pattern) (selected : d188850 q = 1) : d190445 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188850, d190445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188850, d190445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d188851 q = 1) : d190446 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188851, d190446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188851, d190446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d188852 q = 1) : d190447 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188852, d190447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188852, d190447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d188853 q = 1) : d190448 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188853, d190448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188853, d190448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d188854 q = 1) : d190449 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188854, d190449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d188854, d190449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro17585 (p : Pattern) (selected : d188880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6814 q selected
    | true =>
      simp only [d9519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
  have h2 (q : Pattern) (selected : d188877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h4 (q : Pattern) (selected : d188816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188878 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188879 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188880 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17586 (p : Pattern) (selected : d188883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h2 (q : Pattern) (selected : d188816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188879 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188883 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17587 (p : Pattern) (selected : d188889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188881 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17585 q selected
    | true =>
      simp only [d188881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188882 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17586 q selected
    | true =>
      simp only [d188884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d188888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d188889 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d188889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17588 (p : Pattern) (selected : d188893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17586 q selected
    | true =>
      simp only [d188884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188891 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188892 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17589 (p : Pattern) (selected : d188905 p = 1) : d190454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188876 q = 1) : d188876 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d188894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17587 q selected
    | true =>
      simp only [d188894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17588 q selected
  have h3 (q : Pattern) (selected : d188895 q = 1) : d190450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188895, d190450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188895, d190450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188901 q = 1) : d188901 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d188902 q = 1) : d190451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188902, d190451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188902, d190451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188903 q = 1) : d190452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188903, d190452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188903, d190452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d188904 q = 1) : d190453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188904, d190453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188904, d190453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d188905 q = 1) : d190454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188905, d190454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188905, d190454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17590 (p : Pattern) (selected : d188922 p = 1) : d190460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188906 q = 1) : d190455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188906, d190455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188906, d190455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17589 q selected
  have h2 (q : Pattern) (selected : d188917 q = 1) : d188917 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d188918 q = 1) : d190456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188918, d190456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188918, d190456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188919 q = 1) : d190457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188919, d190457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188919, d190457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188920 q = 1) : d190458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188920, d190458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188920, d190458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188921 q = 1) : d190459 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188921, d190459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188921, d190459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188922 q = 1) : d190460 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188922, d190460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188922, d190460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17591 (p : Pattern) (selected : d188928 p = 1) : d190466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188923 q = 1) : d190461 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188923, d190461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188923, d190461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17590 q selected
  have h2 (q : Pattern) (selected : d188924 q = 1) : d190462 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188924, d190462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188924, d190462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188925 q = 1) : d190463 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188925, d190463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188925, d190463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188926 q = 1) : d190464 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188926, d190464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188926, d190464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188927 q = 1) : d190465 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188927, d190465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188927, d190465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188928 q = 1) : d190466 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188928, d190466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188928, d190466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17592 (p : Pattern) (selected : d188959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6825 q selected
    | true =>
      simp only [d9684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
  have h2 (q : Pattern) (selected : d188955 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9688 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
    | true =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6827 q selected
  have h4 (q : Pattern) (selected : d188956 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188957 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188958 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188959 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17593 (p : Pattern) (selected : d188962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9688 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
    | true =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6827 q selected
  have h2 (q : Pattern) (selected : d188956 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d188956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188958 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d188958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188962 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17594 (p : Pattern) (selected : d188968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17592 q selected
    | true =>
      simp only [d188960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188963 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17593 q selected
    | true =>
      simp only [d188963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188964 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d188965 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188966 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d188967 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d188967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d188968 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d188968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17595 (p : Pattern) (selected : d188972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188963 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17593 q selected
    | true =>
      simp only [d188963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d188964 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d188969 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d188969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d188970 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188971 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d188972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d188972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17596 (p : Pattern) (selected : d188984 p = 1) : d190472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188954 q = 1) : d188954 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d188973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17594 q selected
    | true =>
      simp only [d188973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17595 q selected
  have h3 (q : Pattern) (selected : d188974 q = 1) : d190468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188974, d190468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188974, d190468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188980 q = 1) : d188980 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d188981 q = 1) : d190469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188981, d190469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188981, d190469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d188982 q = 1) : d190470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188982, d190470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188982, d190470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d188983 q = 1) : d190471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188983, d190471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188983, d190471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d188984 q = 1) : d190472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188984, d190472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188984, d190472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17597 (p : Pattern) (selected : d189001 p = 1) : d190478 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d188985 q = 1) : d190473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188985, d190473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d188985, d190473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17596 q selected
  have h2 (q : Pattern) (selected : d188996 q = 1) : d188996 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d188997 q = 1) : d190474 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188997, d190474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d188997, d190474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d188998 q = 1) : d190475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188998, d190475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d188998, d190475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d188999 q = 1) : d190476 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188999, d190476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d188999, d190476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189000 q = 1) : d190477 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189000, d190477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189000, d190477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189001 q = 1) : d190478 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189001, d190478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189001, d190478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17598 (p : Pattern) (selected : d189007 p = 1) : d190484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189002 q = 1) : d190479 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189002, d190479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189002, d190479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17597 q selected
  have h2 (q : Pattern) (selected : d189003 q = 1) : d190480 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189003, d190480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189003, d190480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189004 q = 1) : d190481 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189004, d190481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189004, d190481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189005 q = 1) : d190482 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189005, d190482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189005, d190482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189006 q = 1) : d190483 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189006, d190483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189006, d190483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189007 q = 1) : d190484 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189007, d190484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189007, d190484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17599 (p : Pattern) (selected : d189042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9934 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6840 q selected
    | true =>
      simp only [d9934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
  have h2 (q : Pattern) (selected : d189037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9959 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6844 q selected
  have h4 (q : Pattern) (selected : d189038 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189039 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9965 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6845 q selected
  have h7 (q : Pattern) (selected : d189040 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189041 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189042 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17600 (p : Pattern) (selected : d189045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9965 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6845 q selected
  have h2 (q : Pattern) (selected : d189040 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189041 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189045 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17601 (p : Pattern) (selected : d189051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189043 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17599 q selected
    | true =>
      simp only [d189043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189044 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17600 q selected
    | true =>
      simp only [d189046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189048 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189049 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189050 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189051 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17602 (p : Pattern) (selected : d189055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17600 q selected
    | true =>
      simp only [d189046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189052 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189053 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189054 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189055 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17603 (p : Pattern) (selected : d189072 p = 1) : d190491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189036 q = 1) : d189036 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d189056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17601 q selected
    | true =>
      simp only [d189056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17602 q selected
  have h3 (q : Pattern) (selected : d189057 q = 1) : d190487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189057, d190487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189057, d190487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189068 q = 1) : d189068 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d189069 q = 1) : d190488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189069, d190488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189069, d190488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189070 q = 1) : d190489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189070, d190489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189070, d190489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d189071 q = 1) : d190490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189071, d190490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189071, d190490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189072 q = 1) : d190491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189072, d190491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189072, d190491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17604 (p : Pattern) (selected : d189089 p = 1) : d190497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189073 q = 1) : d190492 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189073, d190492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189073, d190492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17603 q selected
  have h2 (q : Pattern) (selected : d189084 q = 1) : d189084 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d189085 q = 1) : d190493 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189085, d190493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189085, d190493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189086 q = 1) : d190494 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189086, d190494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189086, d190494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189087 q = 1) : d190495 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189087, d190495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189087, d190495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189088 q = 1) : d190496 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189088, d190496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189088, d190496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189089 q = 1) : d190497 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189089, d190497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189089, d190497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17605 (p : Pattern) (selected : d189095 p = 1) : d190503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189090 q = 1) : d190498 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189090, d190498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189090, d190498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17604 q selected
  have h2 (q : Pattern) (selected : d189091 q = 1) : d190499 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189091, d190499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189091, d190499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189092 q = 1) : d190500 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189092, d190500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189092, d190500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189093 q = 1) : d190501 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189093, d190501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189093, d190501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189094 q = 1) : d190502 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189094, d190502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189094, d190502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189095 q = 1) : d190503 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189095, d190503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189095, d190503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17606 (p : Pattern) (selected : d189131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6858 q selected
    | true =>
      simp only [d10234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
  have h2 (q : Pattern) (selected : d189126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10262 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6863 q selected
  have h4 (q : Pattern) (selected : d189127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189128 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10271 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6864 q selected
  have h7 (q : Pattern) (selected : d189129 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189130 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189131 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17607 (p : Pattern) (selected : d189134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10271 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6864 q selected
  have h2 (q : Pattern) (selected : d189129 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189130 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189134 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17608 (p : Pattern) (selected : d189140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17606 q selected
    | true =>
      simp only [d189132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17607 q selected
    | true =>
      simp only [d189135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189137 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189138 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189139 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189140 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17609 (p : Pattern) (selected : d189144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17607 q selected
    | true =>
      simp only [d189135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17610 (p : Pattern) (selected : d189161 p = 1) : d190511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189125 q = 1) : d189125 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d189145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17608 q selected
    | true =>
      simp only [d189145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17609 q selected
  have h3 (q : Pattern) (selected : d189146 q = 1) : d190507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189146, d190507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189146, d190507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189157 q = 1) : d189157 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d189158 q = 1) : d190508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189158, d190508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189158, d190508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189159 q = 1) : d190509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189159, d190509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189159, d190509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d189160 q = 1) : d190510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189160, d190510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189160, d190510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189161 q = 1) : d190511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189161, d190511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189161, d190511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17611 (p : Pattern) (selected : d189178 p = 1) : d190517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189162 q = 1) : d190512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189162, d190512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189162, d190512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17610 q selected
  have h2 (q : Pattern) (selected : d189173 q = 1) : d189173 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d189174 q = 1) : d190513 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189174, d190513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189174, d190513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189175 q = 1) : d190514 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189175, d190514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189175, d190514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189176 q = 1) : d190515 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189176, d190515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189176, d190515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189177 q = 1) : d190516 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189177, d190516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189177, d190516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189178 q = 1) : d190517 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189178, d190517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189178, d190517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17612 (p : Pattern) (selected : d189184 p = 1) : d190523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189179 q = 1) : d190518 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189179, d190518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189179, d190518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17611 q selected
  have h2 (q : Pattern) (selected : d189180 q = 1) : d190519 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189180, d190519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189180, d190519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189181 q = 1) : d190520 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189181, d190520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189181, d190520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189182 q = 1) : d190521 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189182, d190521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189182, d190521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189183 q = 1) : d190522 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189183, d190522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189183, d190522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189184 q = 1) : d190523 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189184, d190523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189184, d190523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17613 (p : Pattern) (selected : d189221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10501 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6875 q selected
    | true =>
      simp only [d10501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
  have h2 (q : Pattern) (selected : d189216 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10528 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6880 q selected
  have h4 (q : Pattern) (selected : d189217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6881 q selected
  have h7 (q : Pattern) (selected : d189219 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189220 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d189221 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17614 (p : Pattern) (selected : d189224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6881 q selected
  have h2 (q : Pattern) (selected : d189219 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d189219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189220 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d189220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189224 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d189224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17615 (p : Pattern) (selected : d189230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189222 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17613 q selected
    | true =>
      simp only [d189222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189223 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17614 q selected
    | true =>
      simp only [d189225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d189230 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d189230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17616 (p : Pattern) (selected : d189234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17614 q selected
    | true =>
      simp only [d189225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189234 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17617 (p : Pattern) (selected : d189251 p = 1) : d190532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189215 q = 1) : d189215 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d189235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17615 q selected
    | true =>
      simp only [d189235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17616 q selected
  have h3 (q : Pattern) (selected : d189236 q = 1) : d190528 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189236, d190528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189236, d190528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189247 q = 1) : d189247 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d189248 q = 1) : d190529 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189248, d190529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189248, d190529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189249 q = 1) : d190530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189249, d190530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189249, d190530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d189250 q = 1) : d190531 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189250, d190531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189250, d190531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d189251 q = 1) : d190532 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189251, d190532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189251, d190532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17618 (p : Pattern) (selected : d189268 p = 1) : d190538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189252 q = 1) : d190533 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189252, d190533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189252, d190533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17617 q selected
  have h2 (q : Pattern) (selected : d189263 q = 1) : d189263 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d189264 q = 1) : d190534 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189264, d190534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189264, d190534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189265 q = 1) : d190535 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189265, d190535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189265, d190535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189266 q = 1) : d190536 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189266, d190536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189266, d190536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189267 q = 1) : d190537 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189267, d190537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189267, d190537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d189268 q = 1) : d190538 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189268, d190538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189268, d190538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17619 (p : Pattern) (selected : d189274 p = 1) : d190544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189269 q = 1) : d190539 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189269, d190539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189269, d190539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17618 q selected
  have h2 (q : Pattern) (selected : d189270 q = 1) : d190540 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189270, d190540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189270, d190540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d189271 q = 1) : d190541 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189271, d190541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189271, d190541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189272 q = 1) : d190542 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189272, d190542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189272, d190542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d189273 q = 1) : d190543 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189273, d190543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189273, d190543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189274 q = 1) : d190544 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189274, d190544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189274, d190544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17620 (p : Pattern) (selected : d189280 p = 1) : d190550 p = 1 := by
  have h0 (q : Pattern) (selected : d188929 q = 1) : d190467 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188929, d190467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17584 q selected
    | true =>
      simp only [d188929, d190467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17591 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d189008 q = 1) : d190485 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189008, d190485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189008, d190485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17598 q selected
  have h3 (q : Pattern) (selected : d189009 q = 1) : d190486 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189009, d190486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d189009, d190486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d189096 q = 1) : d190504 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189096, d190504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189096, d190504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17605 q selected
  have h5 (q : Pattern) (selected : d189097 q = 1) : d190505 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189097, d190505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189097, d190505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d189098 q = 1) : d190506 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189098, d190506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189098, d190506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d189185 q = 1) : d190524 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189185, d190524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189185, d190524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17612 q selected
  have h8 (q : Pattern) (selected : d189186 q = 1) : d190525 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189186, d190525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189186, d190525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d189187 q = 1) : d190526 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189187, d190526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189187, d190526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d189188 q = 1) : d190527 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d189188, d190527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d189188, d190527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d189275 q = 1) : d190545 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189275, d190545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189275, d190545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17619 q selected
  have h12 (q : Pattern) (selected : d189276 q = 1) : d190546 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189276, d190546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189276, d190546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d189277 q = 1) : d190547 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189277, d190547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189277, d190547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d189278 q = 1) : d190548 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d189278, d190548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189278, d190548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d189279 q = 1) : d190549 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d189279, d190549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d189279, d190549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d189280 q = 1) : d190550 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d189280, d190550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d189280, d190550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro17621 (p : Pattern) (selected : d189286 p = 1) : d190556 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189281 q = 1) : d190551 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d189281, d190551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17620 q selected
    | true =>
      simp only [d189281, d190551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189282 q = 1) : d190552 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d189282, d190552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189282, d190552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189283 q = 1) : d190553 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d189283, d190553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189283, d190553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189284 q = 1) : d190554 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d189284, d190554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189284, d190554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189285 q = 1) : d190555 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d189285, d190555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189285, d190555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189286 q = 1) : d190556 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d189286, d190556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189286, d190556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17622 (p : Pattern) (selected : d189292 p = 1) : d190562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189287 q = 1) : d190557 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d189287, d190557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17621 q selected
    | true =>
      simp only [d189287, d190557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189288 q = 1) : d190558 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d189288, d190558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189288, d190558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189289 q = 1) : d190559 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d189289, d190559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189289, d190559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189290 q = 1) : d190560 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d189290, d190560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189290, d190560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189291 q = 1) : d190561 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d189291, d190561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189291, d190561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189292 q = 1) : d190562 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d189292, d190562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189292, d190562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17623 (p : Pattern) (selected : d189298 p = 1) : d190568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189293 q = 1) : d190563 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d189293, d190563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17622 q selected
    | true =>
      simp only [d189293, d190563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189294 q = 1) : d190564 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d189294, d190564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189294, d190564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189295 q = 1) : d190565 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d189295, d190565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189295, d190565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189296 q = 1) : d190566 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d189296, d190566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189296, d190566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189297 q = 1) : d190567 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d189297, d190567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189297, d190567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189298 q = 1) : d190568 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d189298, d190568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189298, d190568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17624 (p : Pattern) (selected : d189304 p = 1) : d190574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189299 q = 1) : d190569 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d189299, d190569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17623 q selected
    | true =>
      simp only [d189299, d190569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189300 q = 1) : d190570 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d189300, d190570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189300, d190570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189301 q = 1) : d190571 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d189301, d190571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189301, d190571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189302 q = 1) : d190572 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d189302, d190572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189302, d190572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189303 q = 1) : d190573 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d189303, d190573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189303, d190573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189304 q = 1) : d190574 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d189304, d190574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189304, d190574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17625 (p : Pattern) (selected : d189310 p = 1) : d190580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189305 q = 1) : d190575 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d189305, d190575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17624 q selected
    | true =>
      simp only [d189305, d190575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189306 q = 1) : d190576 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d189306, d190576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189306, d190576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189307 q = 1) : d190577 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d189307, d190577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189307, d190577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189308 q = 1) : d190578 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d189308, d190578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189308, d190578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189309 q = 1) : d190579 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d189309, d190579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189309, d190579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189310 q = 1) : d190580 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d189310, d190580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189310, d190580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17626 (p : Pattern) (selected : d189316 p = 1) : d190586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189311 q = 1) : d190581 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d189311, d190581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17625 q selected
    | true =>
      simp only [d189311, d190581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189312 q = 1) : d190582 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d189312, d190582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189312, d190582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189313 q = 1) : d190583 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d189313, d190583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189313, d190583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189314 q = 1) : d190584 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d189314, d190584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189314, d190584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189315 q = 1) : d190585 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d189315, d190585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189315, d190585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189316 q = 1) : d190586 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d189316, d190586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189316, d190586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17627 (p : Pattern) (selected : d189322 p = 1) : d190592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d189317 q = 1) : d190587 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d189317, d190587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17626 q selected
    | true =>
      simp only [d189317, d190587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d189318 q = 1) : d190588 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d189318, d190588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d189318, d190588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d189319 q = 1) : d190589 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d189319, d190589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189319, d190589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d189320 q = 1) : d190590 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d189320, d190590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d189320, d190590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d189321 q = 1) : d190591 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d189321, d190591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d189321, d190591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d189322 q = 1) : d190592 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d189322, d190592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d189322, d190592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17628 (p : Pattern) (selected : d190635 p = 0) : d191287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173759 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
    | true =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173760 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173761 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173762 q = 0) : d174654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173762, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173762, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173763 q = 0) : d174655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173763, d174655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173763, d174655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190631 q = 0) : d191283 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190631, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190631, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190632 q = 0) : d191284 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190632, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190632, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190633 q = 0) : d191285 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190633, d191285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190633, d191285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190634 q = 0) : d191286 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190634, d191286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190634, d191286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190635 q = 0) : d191287 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190635, d191287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190635, d191287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17629 (p : Pattern) (selected : d190641 p = 0) : d191293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190636 q = 0) : d191288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190636, d191288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17628 q selected
    | true =>
      simp only [d190636, d191288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190637 q = 0) : d191289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190637, d191289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190637, d191289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190638 q = 0) : d191290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190638, d191290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190638, d191290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190639 q = 0) : d191291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190639, d191291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190639, d191291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190640 q = 0) : d191292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190640, d191292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190640, d191292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190641 q = 0) : d191293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190641, d191293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190641, d191293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17630 (p : Pattern) (selected : d190647 p = 0) : d191299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190642 q = 0) : d191294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190642, d191294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17629 q selected
    | true =>
      simp only [d190642, d191294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190643 q = 0) : d191295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190643, d191295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190643, d191295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d190644 q = 0) : d191296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190644, d191296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190644, d191296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190645 q = 0) : d191297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190645, d191297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190645, d191297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190646 q = 0) : d191298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190646, d191298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190646, d191298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190647 q = 0) : d191299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190647, d191299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190647, d191299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17631 (p : Pattern) (selected : d190653 p = 0) : d191305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190648 q = 0) : d191300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190648, d191300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190648, d191300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17630 q selected
  have h2 (q : Pattern) (selected : d190649 q = 0) : d191301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190649, d191301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190649, d191301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d190650 q = 0) : d191302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190650, d191302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190650, d191302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190651 q = 0) : d191303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190651, d191303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190651, d191303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190652 q = 0) : d191304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190652, d191304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190652, d191304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190653 q = 0) : d191305 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190653, d191305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190653, d191305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17632 (p : Pattern) (selected : d190662 p = 0) : d191314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h2 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173759 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
    | true =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173760 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173761 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173793 q = 0) : d174685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173793, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173793, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173762 q = 0) : d174654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173762, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173762, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173794 q = 0) : d174686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173794, d174686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173794, d174686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190658 q = 0) : d191310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190659 q = 0) : d191311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190631 q = 0) : d191283 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190631, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190631, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190632 q = 0) : d191284 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190632, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190632, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190660 q = 0) : d191312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190660, d191312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190660, d191312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190633 q = 0) : d191285 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190633, d191285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190633, d191285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190661 q = 0) : d191313 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190661, d191313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190661, d191313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190662 q = 0) : d191314 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190662, d191314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190662, d191314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17633 (p : Pattern) (selected : d190668 p = 0) : d191320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190663 q = 0) : d191315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190663, d191315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17632 q selected
    | true =>
      simp only [d190663, d191315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190664 q = 0) : d191316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190664, d191316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190664, d191316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190636 q = 0) : d191288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190636, d191288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17628 q selected
    | true =>
      simp only [d190636, d191288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190637 q = 0) : d191289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190637, d191289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190637, d191289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190665 q = 0) : d191317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190665, d191317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190665, d191317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190666 q = 0) : d191318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190666, d191318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190666, d191318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190667 q = 0) : d191319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190667, d191319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190667, d191319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190668 q = 0) : d191320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190668, d191320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190668, d191320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17634 (p : Pattern) (selected : d190674 p = 0) : d191287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173806 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173806, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
    | true =>
      simp only [d173806, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173807 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173807, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173807, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173808 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173808, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173808, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173809 q = 0) : d174654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173809, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173809, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173810 q = 0) : d174655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173810, d174655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173810, d174655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190670 q = 0) : d191283 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190670, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190670, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190671 q = 0) : d191284 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190671, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190671, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190672 q = 0) : d191285 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190672, d191285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190672, d191285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190673 q = 0) : d191286 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190673, d191286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190673, d191286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190674 q = 0) : d191287 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190674, d191287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190674, d191287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17635 (p : Pattern) (selected : d190680 p = 0) : d191293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190675 q = 0) : d191288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190675, d191288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17634 q selected
    | true =>
      simp only [d190675, d191288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190676 q = 0) : d191289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190676, d191289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190676, d191289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190677 q = 0) : d191290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190677, d191290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190677, d191290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190678 q = 0) : d191291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190678, d191291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190678, d191291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190679 q = 0) : d191292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190679, d191292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190679, d191292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190680 q = 0) : d191293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190680, d191293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190680, d191293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17636 (p : Pattern) (selected : d190686 p = 0) : d191326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190669 q = 0) : d191321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190669, d191321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17633 q selected
    | true =>
      simp only [d190669, d191321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17629 q selected
  have h2 (q : Pattern) (selected : d190681 q = 0) : d191294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190681, d191294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17635 q selected
    | true =>
      simp only [d190681, d191294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d190682 q = 0) : d191322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190682, d191322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190682, d191322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190642 q = 0) : d191294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190642, d191294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17629 q selected
    | true =>
      simp only [d190642, d191294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190643 q = 0) : d191295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190643, d191295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190643, d191295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190683 q = 0) : d191323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190683, d191323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190683, d191323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190684 q = 0) : d191324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190684, d191324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190684, d191324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190685 q = 0) : d191325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190685, d191325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190685, d191325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d190686 q = 0) : d191326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190686, d191326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190686, d191326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17637 (p : Pattern) (selected : d190692 p = 0) : d191332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190687 q = 0) : d191327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190687, d191327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190687, d191327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17636 q selected
  have h2 (q : Pattern) (selected : d190688 q = 0) : d191328 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190688, d191328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190688, d191328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d190689 q = 0) : d191329 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190689, d191329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190689, d191329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190690 q = 0) : d191330 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190690, d191330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190690, d191330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190691 q = 0) : d191331 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190691, d191331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190691, d191331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190692 q = 0) : d191332 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190692, d191332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190692, d191332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17638 (p : Pattern) (selected : d190702 p = 0) : d191342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173840 q = 0) : d174716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
    | true =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
  have h2 (q : Pattern) (selected : d173841 q = 0) : d174717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173842 q = 0) : d174718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h5 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173843 q = 0) : d174719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173759 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
    | true =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173760 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173761 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173793 q = 0) : d174685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173793, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173793, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d173844 q = 0) : d174720 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173844, d174720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173844, d174720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d190698 q = 0) : d191338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190698, d191338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190698, d191338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d190699 q = 0) : d191339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190699, d191339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190699, d191339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190658 q = 0) : d191310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190659 q = 0) : d191311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190700 q = 0) : d191340 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190700, d191340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190700, d191340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d190631 q = 0) : d191283 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190631, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190631, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d190632 q = 0) : d191284 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190632, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190632, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d190660 q = 0) : d191312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190660, d191312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d190660, d191312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d190701 q = 0) : d191341 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190701, d191341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d190701, d191341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d190702 q = 0) : d191342 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190702, d191342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d190702, d191342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro17639 (p : Pattern) (selected : d190708 p = 0) : d191348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190703 q = 0) : d191343 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190703, d191343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17638 q selected
    | true =>
      simp only [d190703, d191343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190704 q = 0) : d191344 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190704, d191344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190704, d191344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190663 q = 0) : d191315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190663, d191315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17632 q selected
    | true =>
      simp only [d190663, d191315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190664 q = 0) : d191316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190664, d191316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190664, d191316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190705 q = 0) : d191345 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190705, d191345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190705, d191345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190706 q = 0) : d191346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190706, d191346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190706, d191346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190707 q = 0) : d191347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190707, d191347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190707, d191347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190708 q = 0) : d191348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190708, d191348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190708, d191348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17640 (p : Pattern) (selected : d190714 p = 0) : d191314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173856 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15813 q selected
    | true =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
  have h2 (q : Pattern) (selected : d173857 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173858 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173806 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173806, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
    | true =>
      simp only [d173806, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173807 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173807, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173807, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173808 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173808, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173808, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173859 q = 0) : d174685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173859, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173859, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173809 q = 0) : d174654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173809, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173809, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173860 q = 0) : d174686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173860, d174686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173860, d174686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190710 q = 0) : d191310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190710, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190710, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190711 q = 0) : d191311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190711, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190711, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190670 q = 0) : d191283 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190670, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190670, d191283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190671 q = 0) : d191284 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190671, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190671, d191284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190712 q = 0) : d191312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190712, d191312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190712, d191312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190672 q = 0) : d191285 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190672, d191285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190672, d191285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190713 q = 0) : d191313 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190713, d191313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190713, d191313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190714 q = 0) : d191314 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190714, d191314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190714, d191314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17641 (p : Pattern) (selected : d190720 p = 0) : d191320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190715 q = 0) : d191315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190715, d191315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17640 q selected
    | true =>
      simp only [d190715, d191315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190716 q = 0) : d191316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190716, d191316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190716, d191316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190675 q = 0) : d191288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190675, d191288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17634 q selected
    | true =>
      simp only [d190675, d191288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190676 q = 0) : d191289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190676, d191289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190676, d191289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190717 q = 0) : d191317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190717, d191317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190717, d191317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190718 q = 0) : d191318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190718, d191318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190718, d191318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190719 q = 0) : d191319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190719, d191319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190719, d191319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190720 q = 0) : d191320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190720, d191320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190720, d191320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17642 (p : Pattern) (selected : d190726 p = 0) : d191354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190663 q = 0) : d191315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190663, d191315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17632 q selected
    | true =>
      simp only [d190663, d191315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190664 q = 0) : d191316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190664, d191316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190664, d191316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190723 q = 0) : d191351 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190723, d191351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190723, d191351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190724 q = 0) : d191352 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190724, d191352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190724, d191352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190725 q = 0) : d191353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190725, d191353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190725, d191353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190726 q = 0) : d191354 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190726, d191354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190726, d191354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17643 (p : Pattern) (selected : d190732 p = 0) : d191360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190709 q = 0) : d191349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190709, d191349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17639 q selected
    | true =>
      simp only [d190709, d191349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17633 q selected
  have h2 (q : Pattern) (selected : d190721 q = 0) : d191321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190721, d191321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17641 q selected
    | true =>
      simp only [d190721, d191321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17635 q selected
  have h3 (q : Pattern) (selected : d190722 q = 0) : d191350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190722, d191350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190722, d191350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190727 q = 0) : d191355 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190727, d191355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17642 q selected
    | true =>
      simp only [d190727, d191355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190728 q = 0) : d191356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190728, d191356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190728, d191356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190729 q = 0) : d191357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190729, d191357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190729, d191357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190730 q = 0) : d191358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190730, d191358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190730, d191358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190731 q = 0) : d191359 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190731, d191359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190731, d191359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d190732 q = 0) : d191360 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190732, d191360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190732, d191360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17644 (p : Pattern) (selected : d190738 p = 0) : d191366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190642 q = 0) : d191294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190642, d191294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17629 q selected
    | true =>
      simp only [d190642, d191294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190734 q = 0) : d191362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190734, d191362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190734, d191362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190735 q = 0) : d191363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190735, d191363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190735, d191363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190736 q = 0) : d191364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190736, d191364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190736, d191364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190737 q = 0) : d191365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190737, d191365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190737, d191365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190738 q = 0) : d191366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190738, d191366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190738, d191366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17645 (p : Pattern) (selected : d190744 p = 0) : d191372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190733 q = 0) : d191361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190733, d191361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190733, d191361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17643 q selected
  have h2 (q : Pattern) (selected : d190739 q = 0) : d191367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190739, d191367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190739, d191367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17644 q selected
  have h3 (q : Pattern) (selected : d190740 q = 0) : d191368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190740, d191368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190740, d191368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190741 q = 0) : d191369 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190741, d191369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190741, d191369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190742 q = 0) : d191370 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190742, d191370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190742, d191370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190743 q = 0) : d191371 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190743, d191371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190743, d191371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190744 q = 0) : d191372 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190744, d191372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190744, d191372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17646 (p : Pattern) (selected : d190750 p = 0) : d191378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190654 q = 0) : d191306 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190654, d191306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190654, d191306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17631 q selected
  have h2 (q : Pattern) (selected : d190655 q = 0) : d191307 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190655, d191307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190655, d191307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190656 q = 0) : d191308 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190656, d191308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190656, d191308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190657 q = 0) : d191309 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190657, d191309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190657, d191309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190693 q = 0) : d191333 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190693, d191333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190693, d191333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17637 q selected
  have h6 (q : Pattern) (selected : d190694 q = 0) : d191334 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190694, d191334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190694, d191334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190695 q = 0) : d191335 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190695, d191335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190695, d191335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190696 q = 0) : d191336 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190696, d191336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190696, d191336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d190697 q = 0) : d191337 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190697, d191337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190697, d191337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190745 q = 0) : d191373 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190745, d191373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190745, d191373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17645 q selected
  have h11 (q : Pattern) (selected : d190746 q = 0) : d191374 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190746, d191374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190746, d191374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190747 q = 0) : d191375 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190747, d191375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190747, d191375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d190748 q = 0) : d191376 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190748, d191376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190748, d191376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190749 q = 0) : d191377 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190749, d191377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190749, d191377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190750 q = 0) : d191378 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190750, d191378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190750, d191378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro17647 (p : Pattern) (selected : d190757 p = 0) : d191385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173904 q = 0) : d174764 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173904, d174764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15821 q selected
    | true =>
      simp only [d173904, d174764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
  have h2 (q : Pattern) (selected : d173905 q = 0) : d174765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173905, d174765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173905, d174765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173906 q = 0) : d174766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173906, d174766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173906, d174766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173908 q = 0) : d174768 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173908, d174768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
    | true =>
      simp only [d173908, d174768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15822 q selected
  have h5 (q : Pattern) (selected : d173909 q = 0) : d174769 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173909, d174769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173909, d174769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173910 q = 0) : d174770 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173910, d174770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173910, d174770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173911 q = 0) : d174771 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173911, d174771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173911, d174771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173840 q = 0) : d174716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
    | true =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
  have h9 (q : Pattern) (selected : d173841 q = 0) : d174717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173842 q = 0) : d174718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h12 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d173843 q = 0) : d174719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d173912 q = 0) : d174772 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173912, d174772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173912, d174772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d190751 q = 0) : d191379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190751, d191379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190751, d191379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d190752 q = 0) : d191380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190752, d191380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190752, d191380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d190753 q = 0) : d191381 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190753, d191381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190753, d191381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d190754 q = 0) : d191382 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190754, d191382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190754, d191382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d190755 q = 0) : d191383 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190755, d191383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d190755, d191383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d190698 q = 0) : d191338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190698, d191338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190698, d191338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d190699 q = 0) : d191339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190699, d191339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190699, d191339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d190658 q = 0) : d191310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d190659 q = 0) : d191311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d190700 q = 0) : d191340 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190700, d191340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d190700, d191340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d190756 q = 0) : d191384 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190756, d191384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d190756, d191384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d190757 q = 0) : d191385 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190757, d191385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d190757, d191385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro17648 (p : Pattern) (selected : d190762 p = 0) : d191390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173840 q = 0) : d174716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
    | true =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
  have h2 (q : Pattern) (selected : d173841 q = 0) : d174717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173842 q = 0) : d174718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h5 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173843 q = 0) : d174719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173916 q = 0) : d174776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173916, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173916, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173917 q = 0) : d174777 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173917, d174777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173917, d174777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190698 q = 0) : d191338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190698, d191338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190698, d191338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190699 q = 0) : d191339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190699, d191339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190699, d191339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190658 q = 0) : d191310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190659 q = 0) : d191311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190700 q = 0) : d191340 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190700, d191340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190700, d191340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190760 q = 0) : d191388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190760, d191388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190760, d191388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190761 q = 0) : d191389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190761, d191389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190761, d191389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190762 q = 0) : d191390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190762, d191390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190762, d191390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17649 (p : Pattern) (selected : d190768 p = 0) : d191396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190758 q = 0) : d191386 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190758, d191386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17647 q selected
    | true =>
      simp only [d190758, d191386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190759 q = 0) : d191387 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190759, d191387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190759, d191387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190763 q = 0) : d191391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190763, d191391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17648 q selected
    | true =>
      simp only [d190763, d191391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190764 q = 0) : d191392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190764, d191392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190764, d191392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190765 q = 0) : d191393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190765, d191393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190765, d191393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190766 q = 0) : d191394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190766, d191394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190766, d191394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190767 q = 0) : d191395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190767, d191395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190767, d191395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190768 q = 0) : d191396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190768, d191396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190768, d191396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17650 (p : Pattern) (selected : d190770 p = 0) : d191398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h2 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173916 q = 0) : d174776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173916, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173916, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173925 q = 0) : d174785 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173925, d174785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173925, d174785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190658 q = 0) : d191310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190658, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190659 q = 0) : d191311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190659, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190760 q = 0) : d191388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190760, d191388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190760, d191388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190769 q = 0) : d191397 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190769, d191397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190769, d191397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190770 q = 0) : d191398 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190770, d191398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190770, d191398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17651 (p : Pattern) (selected : d190776 p = 0) : d191404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190763 q = 0) : d191391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190763, d191391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17648 q selected
    | true =>
      simp only [d190763, d191391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190764 q = 0) : d191392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190764, d191392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190764, d191392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190771 q = 0) : d191399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190771, d191399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17650 q selected
    | true =>
      simp only [d190771, d191399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190772 q = 0) : d191400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190772, d191400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190772, d191400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190773 q = 0) : d191401 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190773, d191401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190773, d191401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190774 q = 0) : d191402 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190774, d191402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190774, d191402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190775 q = 0) : d191403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190775, d191403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190775, d191403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190776 q = 0) : d191404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190776, d191404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190776, d191404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17652 (p : Pattern) (selected : d190783 p = 0) : d191390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173939 q = 0) : d174716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173939, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15828 q selected
    | true =>
      simp only [d173939, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15813 q selected
  have h2 (q : Pattern) (selected : d173940 q = 0) : d174717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173940, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173940, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173941 q = 0) : d174718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173941, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173941, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173856 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15813 q selected
    | true =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
  have h5 (q : Pattern) (selected : d173857 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173858 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173942 q = 0) : d174719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173942, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173942, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173943 q = 0) : d174776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173943, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173943, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173944 q = 0) : d174777 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173944, d174777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173944, d174777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190778 q = 0) : d191338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190778, d191338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190778, d191338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190779 q = 0) : d191339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190779, d191339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190779, d191339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190710 q = 0) : d191310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190710, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190710, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190711 q = 0) : d191311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190711, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190711, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190780 q = 0) : d191340 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190780, d191340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190780, d191340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190781 q = 0) : d191388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190781, d191388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190781, d191388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190782 q = 0) : d191389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190782, d191389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190782, d191389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190783 q = 0) : d191390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190783, d191390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190783, d191390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17653 (p : Pattern) (selected : d190787 p = 0) : d191398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173856 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15813 q selected
    | true =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
  have h2 (q : Pattern) (selected : d173857 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173858 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173943 q = 0) : d174776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173943, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173943, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173948 q = 0) : d174785 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173948, d174785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173948, d174785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190710 q = 0) : d191310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190710, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190710, d191310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190711 q = 0) : d191311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190711, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190711, d191311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190781 q = 0) : d191388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190781, d191388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190781, d191388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190786 q = 0) : d191397 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190786, d191397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190786, d191397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190787 q = 0) : d191398 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190787, d191398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190787, d191398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17654 (p : Pattern) (selected : d190793 p = 0) : d191404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190784 q = 0) : d191391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190784, d191391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17652 q selected
    | true =>
      simp only [d190784, d191391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190785 q = 0) : d191392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190785, d191392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190785, d191392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190788 q = 0) : d191399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190788, d191399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17653 q selected
    | true =>
      simp only [d190788, d191399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190789 q = 0) : d191400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190789, d191400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190789, d191400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190790 q = 0) : d191401 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190790, d191401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190790, d191401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190791 q = 0) : d191402 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190791, d191402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190791, d191402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190792 q = 0) : d191403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190792, d191403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190792, d191403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190793 q = 0) : d191404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190793, d191404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190793, d191404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17655 (p : Pattern) (selected : d190797 p = 0) : d191409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190788 q = 0) : d191399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190788, d191399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17653 q selected
    | true =>
      simp only [d190788, d191399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190789 q = 0) : d191400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190789, d191400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190789, d191400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190794 q = 0) : d191406 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190794, d191406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190794, d191406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190795 q = 0) : d191407 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190795, d191407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190795, d191407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190796 q = 0) : d191408 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190796, d191408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190796, d191408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190797 q = 0) : d191409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190797, d191409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190797, d191409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17656 (p : Pattern) (selected : d190803 p = 0) : d191415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190763 q = 0) : d191391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190763, d191391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17648 q selected
    | true =>
      simp only [d190763, d191391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190764 q = 0) : d191392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190764, d191392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190764, d191392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190800 q = 0) : d191412 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190800, d191412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190800, d191412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190801 q = 0) : d191413 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190801, d191413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190801, d191413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190802 q = 0) : d191414 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190802, d191414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190802, d191414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190803 q = 0) : d191415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190803, d191415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190803, d191415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17657 (p : Pattern) (selected : d190809 p = 0) : d191421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190777 q = 0) : d191405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190777, d191405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17649 q selected
    | true =>
      simp only [d190777, d191405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17651 q selected
  have h2 (q : Pattern) (selected : d190798 q = 0) : d191410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190798, d191410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17654 q selected
    | true =>
      simp only [d190798, d191410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17655 q selected
  have h3 (q : Pattern) (selected : d190799 q = 0) : d191411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190799, d191411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190799, d191411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190804 q = 0) : d191416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190804, d191416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17656 q selected
    | true =>
      simp only [d190804, d191416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190805 q = 0) : d191417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190805, d191417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190805, d191417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190806 q = 0) : d191418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190806, d191418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190806, d191418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190807 q = 0) : d191419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190807, d191419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190807, d191419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190808 q = 0) : d191420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190808, d191420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190808, d191420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d190809 q = 0) : d191421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190809, d191421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190809, d191421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17658 (p : Pattern) (selected : d190814 p = 0) : d191409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190771 q = 0) : d191399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190771, d191399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17650 q selected
    | true =>
      simp only [d190771, d191399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190772 q = 0) : d191400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190772, d191400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190772, d191400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190811 q = 0) : d191406 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190811, d191406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190811, d191406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190812 q = 0) : d191407 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190812, d191407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190812, d191407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190813 q = 0) : d191408 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190813, d191408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190813, d191408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190814 q = 0) : d191409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190814, d191409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190814, d191409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17659 (p : Pattern) (selected : d190820 p = 0) : d191428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190815 q = 0) : d191423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190815, d191423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17658 q selected
    | true =>
      simp only [d190815, d191423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190816 q = 0) : d191424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190816, d191424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190816, d191424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190817 q = 0) : d191425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190817, d191425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190817, d191425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190818 q = 0) : d191426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190818, d191426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190818, d191426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190819 q = 0) : d191427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190819, d191427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190819, d191427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190820 q = 0) : d191428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190820, d191428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190820, d191428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17660 (p : Pattern) (selected : d190826 p = 0) : d191434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190810 q = 0) : d191422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190810, d191422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190810, d191422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17657 q selected
  have h2 (q : Pattern) (selected : d190821 q = 0) : d191429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190821, d191429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190821, d191429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17659 q selected
  have h3 (q : Pattern) (selected : d190822 q = 0) : d191430 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190822, d191430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190822, d191430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190823 q = 0) : d191431 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190823, d191431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190823, d191431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190824 q = 0) : d191432 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190824, d191432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190824, d191432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190825 q = 0) : d191433 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190825, d191433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190825, d191433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190826 q = 0) : d191434 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190826, d191434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190826, d191434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17661 (p : Pattern) (selected : d190832 p = 0) : d191440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190827 q = 0) : d191435 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190827, d191435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190827, d191435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17660 q selected
  have h2 (q : Pattern) (selected : d190828 q = 0) : d191436 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190828, d191436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190828, d191436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190829 q = 0) : d191437 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190829, d191437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190829, d191437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190830 q = 0) : d191438 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190830, d191438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190830, d191438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190831 q = 0) : d191439 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190831, d191439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190831, d191439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190832 q = 0) : d191440 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190832, d191440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190832, d191440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17662 (p : Pattern) (selected : d190845 p = 0) : d191453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174005 q = 0) : d174839 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174005, d174839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15839 q selected
    | true =>
      simp only [d174005, d174839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15840 q selected
  have h2 (q : Pattern) (selected : d174006 q = 0) : d174840 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174006, d174840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174006, d174840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174007 q = 0) : d174841 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174007, d174841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174007, d174841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174010 q = 0) : d174844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174010, d174844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15840 q selected
    | true =>
      simp only [d174010, d174844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15841 q selected
  have h5 (q : Pattern) (selected : d174011 q = 0) : d174845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174011, d174845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174011, d174845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174012 q = 0) : d174846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174012, d174846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174012, d174846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174013 q = 0) : d174847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174013, d174847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174013, d174847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174016 q = 0) : d174850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174016, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15840 q selected
    | true =>
      simp only [d174016, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
  have h9 (q : Pattern) (selected : d174017 q = 0) : d174851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174017, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174017, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174018 q = 0) : d174852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174018, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174018, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174020 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
    | true =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15843 q selected
  have h12 (q : Pattern) (selected : d174021 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174022 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174023 q = 0) : d174857 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174023, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174023, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174024 q = 0) : d174858 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174024, d174858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174024, d174858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d190834 q = 0) : d191442 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190834, d191442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190834, d191442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d190835 q = 0) : d191443 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190835, d191443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190835, d191443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d190836 q = 0) : d191444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190836, d191444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190836, d191444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d190837 q = 0) : d191445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190837, d191445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190837, d191445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d190838 q = 0) : d191446 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190838, d191446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d190838, d191446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d190839 q = 0) : d191447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190839, d191447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190839, d191447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d190840 q = 0) : d191448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190840, d191448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190840, d191448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d190841 q = 0) : d191449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190841, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190841, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d190842 q = 0) : d191450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190842, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190842, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d190843 q = 0) : d191451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190843, d191451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d190843, d191451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d190844 q = 0) : d191452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190844, d191452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d190844, d191452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d190845 q = 0) : d191453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190845, d191453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d190845, d191453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro17663 (p : Pattern) (selected : d190850 p = 0) : d191458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174016 q = 0) : d174850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174016, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15840 q selected
    | true =>
      simp only [d174016, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
  have h2 (q : Pattern) (selected : d174017 q = 0) : d174851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174017, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174017, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174018 q = 0) : d174852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174018, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174018, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174020 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
    | true =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15843 q selected
  have h5 (q : Pattern) (selected : d174021 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174022 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174023 q = 0) : d174857 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174023, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174023, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174028 q = 0) : d174862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174028, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174028, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174029 q = 0) : d174863 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174029, d174863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174029, d174863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190839 q = 0) : d191447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190839, d191447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190839, d191447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190840 q = 0) : d191448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190840, d191448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190840, d191448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190841 q = 0) : d191449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190841, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190841, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190842 q = 0) : d191450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190842, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190842, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190843 q = 0) : d191451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190843, d191451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190843, d191451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190848 q = 0) : d191456 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190848, d191456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190848, d191456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190849 q = 0) : d191457 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190849, d191457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190849, d191457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190850 q = 0) : d191458 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190850, d191458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190850, d191458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17664 (p : Pattern) (selected : d190856 p = 0) : d191464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190846 q = 0) : d191454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190846, d191454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17662 q selected
    | true =>
      simp only [d190846, d191454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190847 q = 0) : d191455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190847, d191455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190847, d191455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190851 q = 0) : d191459 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190851, d191459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17663 q selected
    | true =>
      simp only [d190851, d191459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190852 q = 0) : d191460 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190852, d191460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190852, d191460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190853 q = 0) : d191461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190853, d191461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190853, d191461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190854 q = 0) : d191462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190854, d191462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190854, d191462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190855 q = 0) : d191463 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190855, d191463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190855, d191463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190856 q = 0) : d191464 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190856, d191464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190856, d191464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17665 (p : Pattern) (selected : d190858 p = 0) : d191466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174020 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
    | true =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15843 q selected
  have h2 (q : Pattern) (selected : d174021 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174022 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174028 q = 0) : d174862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174028, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174028, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174037 q = 0) : d174871 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174037, d174871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174037, d174871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190841 q = 0) : d191449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190841, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190841, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190842 q = 0) : d191450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190842, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190842, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190848 q = 0) : d191456 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190848, d191456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190848, d191456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190857 q = 0) : d191465 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190857, d191465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190857, d191465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190858 q = 0) : d191466 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190858, d191466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190858, d191466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17666 (p : Pattern) (selected : d190864 p = 0) : d191472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190851 q = 0) : d191459 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190851, d191459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17663 q selected
    | true =>
      simp only [d190851, d191459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190852 q = 0) : d191460 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190852, d191460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190852, d191460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190859 q = 0) : d191467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190859, d191467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17665 q selected
    | true =>
      simp only [d190859, d191467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190860 q = 0) : d191468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190860, d191468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190860, d191468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190861 q = 0) : d191469 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190861, d191469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190861, d191469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190862 q = 0) : d191470 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190862, d191470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190862, d191470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190863 q = 0) : d191471 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190863, d191471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190863, d191471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190864 q = 0) : d191472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190864, d191472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190864, d191472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17667 (p : Pattern) (selected : d190873 p = 0) : d191458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174056 q = 0) : d174850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174056, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15849 q selected
    | true =>
      simp only [d174056, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15850 q selected
  have h2 (q : Pattern) (selected : d174057 q = 0) : d174851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174057, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174057, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174058 q = 0) : d174852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174058, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174058, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174060 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174060, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15850 q selected
    | true =>
      simp only [d174060, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15851 q selected
  have h5 (q : Pattern) (selected : d174061 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174061, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174061, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174062 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174062, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174062, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174063 q = 0) : d174857 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174063, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174063, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174064 q = 0) : d174862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174064, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174064, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174065 q = 0) : d174863 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174065, d174863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174065, d174863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190866 q = 0) : d191447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190866, d191447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190866, d191447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190867 q = 0) : d191448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190867, d191448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190867, d191448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190868 q = 0) : d191449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190868, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190868, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190869 q = 0) : d191450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190869, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190869, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190870 q = 0) : d191451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190870, d191451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190870, d191451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190871 q = 0) : d191456 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190871, d191456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190871, d191456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190872 q = 0) : d191457 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190872, d191457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190872, d191457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190873 q = 0) : d191458 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190873, d191458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190873, d191458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17668 (p : Pattern) (selected : d190877 p = 0) : d191466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174060 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174060, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15850 q selected
    | true =>
      simp only [d174060, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15851 q selected
  have h2 (q : Pattern) (selected : d174061 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174061, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174061, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174062 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174062, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174062, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174064 q = 0) : d174862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174064, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174064, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174069 q = 0) : d174871 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174069, d174871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174069, d174871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190868 q = 0) : d191449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190868, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190868, d191449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190869 q = 0) : d191450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190869, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190869, d191450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190871 q = 0) : d191456 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190871, d191456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190871, d191456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190876 q = 0) : d191465 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190876, d191465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190876, d191465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190877 q = 0) : d191466 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190877, d191466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190877, d191466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17669 (p : Pattern) (selected : d190883 p = 0) : d191472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190874 q = 0) : d191459 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190874, d191459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17667 q selected
    | true =>
      simp only [d190874, d191459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190875 q = 0) : d191460 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190875, d191460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190875, d191460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190878 q = 0) : d191467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190878, d191467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17668 q selected
    | true =>
      simp only [d190878, d191467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190879 q = 0) : d191468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190879, d191468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190879, d191468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190880 q = 0) : d191469 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190880, d191469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190880, d191469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190881 q = 0) : d191470 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190881, d191470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190881, d191470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190882 q = 0) : d191471 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190882, d191471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190882, d191471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190883 q = 0) : d191472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190883, d191472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190883, d191472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17670 (p : Pattern) (selected : d190887 p = 0) : d191477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190878 q = 0) : d191467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190878, d191467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17668 q selected
    | true =>
      simp only [d190878, d191467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190879 q = 0) : d191468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190879, d191468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190879, d191468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190884 q = 0) : d191474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190884, d191474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190884, d191474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190885 q = 0) : d191475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190885, d191475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190885, d191475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190886 q = 0) : d191476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190886, d191476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190886, d191476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190887 q = 0) : d191477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190887, d191477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190887, d191477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17671 (p : Pattern) (selected : d190893 p = 0) : d191483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190851 q = 0) : d191459 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190851, d191459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17663 q selected
    | true =>
      simp only [d190851, d191459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190852 q = 0) : d191460 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190852, d191460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190852, d191460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190890 q = 0) : d191480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190890, d191480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190890, d191480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190891 q = 0) : d191481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190891, d191481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190891, d191481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190892 q = 0) : d191482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190892, d191482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190892, d191482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190893 q = 0) : d191483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190893, d191483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190893, d191483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17672 (p : Pattern) (selected : d190899 p = 0) : d191489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190865 q = 0) : d191473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190865, d191473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17664 q selected
    | true =>
      simp only [d190865, d191473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17666 q selected
  have h2 (q : Pattern) (selected : d190888 q = 0) : d191478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190888, d191478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17669 q selected
    | true =>
      simp only [d190888, d191478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17670 q selected
  have h3 (q : Pattern) (selected : d190889 q = 0) : d191479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190889, d191479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190889, d191479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190894 q = 0) : d191484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190894, d191484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17671 q selected
    | true =>
      simp only [d190894, d191484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190895 q = 0) : d191485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190895, d191485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190895, d191485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190896 q = 0) : d191486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190896, d191486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190896, d191486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190897 q = 0) : d191487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190897, d191487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190897, d191487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190898 q = 0) : d191488 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190898, d191488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190898, d191488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d190899 q = 0) : d191489 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190899, d191489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190899, d191489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17673 (p : Pattern) (selected : d190904 p = 0) : d191477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190859 q = 0) : d191467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190859, d191467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17665 q selected
    | true =>
      simp only [d190859, d191467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190860 q = 0) : d191468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190860, d191468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190860, d191468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190901 q = 0) : d191474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190901, d191474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190901, d191474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190902 q = 0) : d191475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190902, d191475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190902, d191475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190903 q = 0) : d191476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190903, d191476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190903, d191476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190904 q = 0) : d191477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190904, d191477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190904, d191477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17674 (p : Pattern) (selected : d190910 p = 0) : d191496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190905 q = 0) : d191491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190905, d191491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17673 q selected
    | true =>
      simp only [d190905, d191491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190906 q = 0) : d191492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190906, d191492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190906, d191492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190907 q = 0) : d191493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190907, d191493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190907, d191493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190908 q = 0) : d191494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190908, d191494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190908, d191494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190909 q = 0) : d191495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190909, d191495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190909, d191495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190910 q = 0) : d191496 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190910, d191496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190910, d191496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17675 (p : Pattern) (selected : d190916 p = 0) : d191502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190900 q = 0) : d191490 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190900, d191490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190900, d191490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17672 q selected
  have h2 (q : Pattern) (selected : d190911 q = 0) : d191497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190911, d191497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190911, d191497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17674 q selected
  have h3 (q : Pattern) (selected : d190912 q = 0) : d191498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190912, d191498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190912, d191498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190913 q = 0) : d191499 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190913, d191499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190913, d191499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190914 q = 0) : d191500 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190914, d191500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190914, d191500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190915 q = 0) : d191501 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190915, d191501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190915, d191501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190916 q = 0) : d191502 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190916, d191502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190916, d191502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17676 (p : Pattern) (selected : d190922 p = 0) : d191508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190917 q = 0) : d191503 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190917, d191503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190917, d191503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17675 q selected
  have h2 (q : Pattern) (selected : d190918 q = 0) : d191504 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190918, d191504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190918, d191504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190919 q = 0) : d191505 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190919, d191505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190919, d191505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190920 q = 0) : d191506 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190920, d191506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190920, d191506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190921 q = 0) : d191507 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190921, d191507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190921, d191507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190922 q = 0) : d191508 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190922, d191508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190922, d191508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17677 (p : Pattern) (selected : d190936 p = 0) : d191522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174131 q = 0) : d174930 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174131, d174930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15862 q selected
    | true =>
      simp only [d174131, d174930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
  have h2 (q : Pattern) (selected : d174132 q = 0) : d174931 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174132, d174931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174132, d174931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174133 q = 0) : d174932 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174133, d174932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174133, d174932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174138 q = 0) : d174937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174138, d174937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
    | true =>
      simp only [d174138, d174937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15864 q selected
  have h5 (q : Pattern) (selected : d174139 q = 0) : d174938 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174139, d174938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174139, d174938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174140 q = 0) : d174939 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174140, d174939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174140, d174939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174141 q = 0) : d174940 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174141, d174940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174141, d174940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174146 q = 0) : d174945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
    | true =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
  have h9 (q : Pattern) (selected : d174147 q = 0) : d174946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174148 q = 0) : d174947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174154 q = 0) : d174953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15866 q selected
  have h12 (q : Pattern) (selected : d174155 q = 0) : d174954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174156 q = 0) : d174955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174157 q = 0) : d174956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174158 q = 0) : d174957 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174158, d174957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174158, d174957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d190925 q = 0) : d191511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190925, d191511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190925, d191511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d190926 q = 0) : d191512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190926, d191512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190926, d191512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d190927 q = 0) : d191513 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190927, d191513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190927, d191513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d190928 q = 0) : d191514 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190928, d191514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190928, d191514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d190929 q = 0) : d191515 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190929, d191515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d190929, d191515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d190930 q = 0) : d191516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190930, d191516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190930, d191516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d190931 q = 0) : d191517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190931, d191517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190931, d191517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d190932 q = 0) : d191518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190932, d191518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190932, d191518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d190933 q = 0) : d191519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190933, d191519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190933, d191519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d190934 q = 0) : d191520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190934, d191520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d190934, d191520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d190935 q = 0) : d191521 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190935, d191521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d190935, d191521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d190936 q = 0) : d191522 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190936, d191522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d190936, d191522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro17678 (p : Pattern) (selected : d190941 p = 0) : d191527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174146 q = 0) : d174945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
    | true =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
  have h2 (q : Pattern) (selected : d174147 q = 0) : d174946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174148 q = 0) : d174947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174154 q = 0) : d174953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15866 q selected
  have h5 (q : Pattern) (selected : d174155 q = 0) : d174954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174156 q = 0) : d174955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174157 q = 0) : d174956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174162 q = 0) : d174961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174162, d174961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174162, d174961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174163 q = 0) : d174962 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174163, d174962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174163, d174962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190930 q = 0) : d191516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190930, d191516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190930, d191516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190931 q = 0) : d191517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190931, d191517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190931, d191517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190932 q = 0) : d191518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190932, d191518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190932, d191518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190933 q = 0) : d191519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190933, d191519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190933, d191519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190934 q = 0) : d191520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190934, d191520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190934, d191520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190939 q = 0) : d191525 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190939, d191525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190939, d191525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190940 q = 0) : d191526 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190940, d191526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190940, d191526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190941 q = 0) : d191527 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190941, d191527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190941, d191527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17679 (p : Pattern) (selected : d190947 p = 0) : d191533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190937 q = 0) : d191523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190937, d191523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17677 q selected
    | true =>
      simp only [d190937, d191523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190938 q = 0) : d191524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190938, d191524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190938, d191524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190942 q = 0) : d191528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190942, d191528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17678 q selected
    | true =>
      simp only [d190942, d191528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190943 q = 0) : d191529 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190943, d191529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190943, d191529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190944 q = 0) : d191530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190944, d191530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190944, d191530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190945 q = 0) : d191531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190945, d191531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190945, d191531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190946 q = 0) : d191532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190946, d191532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190946, d191532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190947 q = 0) : d191533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190947, d191533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190947, d191533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17680 (p : Pattern) (selected : d190952 p = 0) : d191538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174173 q = 0) : d174972 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174173, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174173, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15870 q selected
  have h2 (q : Pattern) (selected : d174174 q = 0) : d174973 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174174, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174174, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174175 q = 0) : d174974 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174175, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174175, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174176 q = 0) : d174975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174176, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174176, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174177 q = 0) : d174976 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174177, d174976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174177, d174976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190948 q = 0) : d191534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190948, d191534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190948, d191534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190949 q = 0) : d191535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190949, d191535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190949, d191535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190950 q = 0) : d191536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190950, d191536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190950, d191536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190951 q = 0) : d191537 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190951, d191537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190951, d191537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190952 q = 0) : d191538 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190952, d191538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190952, d191538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17681 (p : Pattern) (selected : d190958 p = 0) : d191544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190942 q = 0) : d191528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190942, d191528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17678 q selected
    | true =>
      simp only [d190942, d191528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190943 q = 0) : d191529 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190943, d191529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190943, d191529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190953 q = 0) : d191539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190953, d191539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17680 q selected
    | true =>
      simp only [d190953, d191539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190954 q = 0) : d191540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190954, d191540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190954, d191540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190955 q = 0) : d191541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190955, d191541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190955, d191541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190956 q = 0) : d191542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190956, d191542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190956, d191542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190957 q = 0) : d191543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190957, d191543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190957, d191543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190958 q = 0) : d191544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190958, d191544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190958, d191544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17682 (p : Pattern) (selected : d190969 p = 0) : d191547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174198 q = 0) : d174945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174198, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15873 q selected
    | true =>
      simp only [d174198, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15874 q selected
  have h2 (q : Pattern) (selected : d174199 q = 0) : d174946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174199, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174199, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174200 q = 0) : d174947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174200, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174200, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174206 q = 0) : d174953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174206, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15874 q selected
    | true =>
      simp only [d174206, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15875 q selected
  have h5 (q : Pattern) (selected : d174207 q = 0) : d174954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174207, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174207, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174208 q = 0) : d174955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174208, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174208, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174209 q = 0) : d174956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174209, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174209, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174212 q = 0) : d174972 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174212, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15874 q selected
    | true =>
      simp only [d174212, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15876 q selected
  have h9 (q : Pattern) (selected : d174213 q = 0) : d174973 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174213, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174213, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174214 q = 0) : d174974 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174214, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174214, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174215 q = 0) : d174975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174215, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174215, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174216 q = 0) : d174985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174216, d174985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174216, d174985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d190960 q = 0) : d191516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190960, d191516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190960, d191516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d190961 q = 0) : d191517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190961, d191517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190961, d191517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190962 q = 0) : d191518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190962, d191518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190962, d191518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190963 q = 0) : d191519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190963, d191519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190963, d191519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190964 q = 0) : d191520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190964, d191520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190964, d191520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d190965 q = 0) : d191534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190965, d191534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190965, d191534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d190966 q = 0) : d191535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190966, d191535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190966, d191535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d190967 q = 0) : d191536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190967, d191536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d190967, d191536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d190968 q = 0) : d191546 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190968, d191546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d190968, d191546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d190969 q = 0) : d191547 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190969, d191547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d190969, d191547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro17683 (p : Pattern) (selected : d190973 p = 0) : d191538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174212 q = 0) : d174972 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174212, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15874 q selected
    | true =>
      simp only [d174212, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15876 q selected
  have h2 (q : Pattern) (selected : d174213 q = 0) : d174973 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174213, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174213, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174214 q = 0) : d174974 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174214, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174214, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174215 q = 0) : d174975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174215, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174215, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174220 q = 0) : d174976 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174220, d174976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174220, d174976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190965 q = 0) : d191534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190965, d191534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190965, d191534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190966 q = 0) : d191535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190966, d191535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190966, d191535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190967 q = 0) : d191536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190967, d191536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190967, d191536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190972 q = 0) : d191537 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190972, d191537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190972, d191537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190973 q = 0) : d191538 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190973, d191538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190973, d191538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17684 (p : Pattern) (selected : d190979 p = 0) : d191553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190970 q = 0) : d191548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190970, d191548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17682 q selected
    | true =>
      simp only [d190970, d191548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190971 q = 0) : d191549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190971, d191549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190971, d191549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190974 q = 0) : d191539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190974, d191539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17683 q selected
    | true =>
      simp only [d190974, d191539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190975 q = 0) : d191540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190975, d191540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190975, d191540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190976 q = 0) : d191550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190976, d191550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190976, d191550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190977 q = 0) : d191551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190977, d191551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190977, d191551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190978 q = 0) : d191552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190978, d191552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190978, d191552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190979 q = 0) : d191553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190979, d191553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190979, d191553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17685 (p : Pattern) (selected : d190983 p = 0) : d191557 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190974 q = 0) : d191539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190974, d191539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17683 q selected
    | true =>
      simp only [d190974, d191539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190975 q = 0) : d191540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190975, d191540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190975, d191540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190980 q = 0) : d191554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190980, d191554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190980, d191554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190981 q = 0) : d191555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190981, d191555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190981, d191555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190982 q = 0) : d191556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190982, d191556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190982, d191556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190983 q = 0) : d191557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190983, d191557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190983, d191557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17686 (p : Pattern) (selected : d190990 p = 0) : d191564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174146 q = 0) : d174945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
    | true =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
  have h2 (q : Pattern) (selected : d174147 q = 0) : d174946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174148 q = 0) : d174947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174154 q = 0) : d174953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15866 q selected
  have h5 (q : Pattern) (selected : d174155 q = 0) : d174954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174156 q = 0) : d174955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174157 q = 0) : d174956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174235 q = 0) : d175000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174235, d175000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174235, d175000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15881 q selected
  have h9 (q : Pattern) (selected : d174236 q = 0) : d175001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174236, d175001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174236, d175001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174237 q = 0) : d175002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174237, d175002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174237, d175002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174238 q = 0) : d175003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174238, d175003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174238, d175003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174239 q = 0) : d175004 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174239, d175004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174239, d175004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d190930 q = 0) : d191516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190930, d191516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190930, d191516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d190931 q = 0) : d191517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190931, d191517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190931, d191517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190932 q = 0) : d191518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190932, d191518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190932, d191518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190933 q = 0) : d191519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190933, d191519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190933, d191519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190934 q = 0) : d191520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190934, d191520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190934, d191520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d190986 q = 0) : d191560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190986, d191560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190986, d191560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d190987 q = 0) : d191561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190987, d191561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190987, d191561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d190988 q = 0) : d191562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190988, d191562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d190988, d191562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d190989 q = 0) : d191563 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190989, d191563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d190989, d191563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d190990 q = 0) : d191564 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190990, d191564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d190990, d191564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro17687 (p : Pattern) (selected : d190996 p = 0) : d191570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190991 q = 0) : d191565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190991, d191565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17686 q selected
    | true =>
      simp only [d190991, d191565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190992 q = 0) : d191566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190992, d191566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190992, d191566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190993 q = 0) : d191567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190993, d191567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190993, d191567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190994 q = 0) : d191568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190994, d191568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190994, d191568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190995 q = 0) : d191569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190995, d191569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190995, d191569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190996 q = 0) : d191570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190996, d191570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190996, d191570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17688 (p : Pattern) (selected : d191002 p = 0) : d191576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190959 q = 0) : d191545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190959, d191545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17679 q selected
    | true =>
      simp only [d190959, d191545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17681 q selected
  have h2 (q : Pattern) (selected : d190984 q = 0) : d191558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190984, d191558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17684 q selected
    | true =>
      simp only [d190984, d191558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17685 q selected
  have h3 (q : Pattern) (selected : d190985 q = 0) : d191559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190985, d191559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190985, d191559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190997 q = 0) : d191571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190997, d191571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17687 q selected
    | true =>
      simp only [d190997, d191571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190998 q = 0) : d191572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190998, d191572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190998, d191572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190999 q = 0) : d191573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190999, d191573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190999, d191573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d191000 q = 0) : d191574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191000, d191574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191000, d191574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d191001 q = 0) : d191575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191001, d191575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191001, d191575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d191002 q = 0) : d191576 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191002, d191576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191002, d191576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17689 (p : Pattern) (selected : d191007 p = 0) : d191557 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d190953 q = 0) : d191539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190953, d191539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17680 q selected
    | true =>
      simp only [d190953, d191539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190954 q = 0) : d191540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190954, d191540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190954, d191540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191004 q = 0) : d191554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191004, d191554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191004, d191554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191005 q = 0) : d191555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191005, d191555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191005, d191555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191006 q = 0) : d191556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191006, d191556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191006, d191556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191007 q = 0) : d191557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191007, d191557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191007, d191557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17690 (p : Pattern) (selected : d191013 p = 0) : d191583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191008 q = 0) : d191578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191008, d191578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17689 q selected
    | true =>
      simp only [d191008, d191578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191009 q = 0) : d191579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191009, d191579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191009, d191579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191010 q = 0) : d191580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191010, d191580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191010, d191580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191011 q = 0) : d191581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191011, d191581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191011, d191581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191012 q = 0) : d191582 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191012, d191582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191012, d191582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191013 q = 0) : d191583 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191013, d191583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191013, d191583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17691 (p : Pattern) (selected : d191019 p = 0) : d191589 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191003 q = 0) : d191577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191003, d191577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191003, d191577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17688 q selected
  have h2 (q : Pattern) (selected : d191014 q = 0) : d191584 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191014, d191584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191014, d191584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17690 q selected
  have h3 (q : Pattern) (selected : d191015 q = 0) : d191585 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191015, d191585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191015, d191585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191016 q = 0) : d191586 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191016, d191586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191016, d191586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191017 q = 0) : d191587 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191017, d191587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191017, d191587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191018 q = 0) : d191588 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191018, d191588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191018, d191588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191019 q = 0) : d191589 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191019, d191589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191019, d191589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17692 (p : Pattern) (selected : d191025 p = 0) : d191595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191020 q = 0) : d191590 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191020, d191590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191020, d191590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17691 q selected
  have h2 (q : Pattern) (selected : d191021 q = 0) : d191591 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191021, d191591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191021, d191591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191022 q = 0) : d191592 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191022, d191592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191022, d191592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191023 q = 0) : d191593 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191023, d191593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191023, d191593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191024 q = 0) : d191594 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191024, d191594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191024, d191594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191025 q = 0) : d191595 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191025, d191595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191025, d191595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17693 (p : Pattern) (selected : d191040 p = 0) : d191610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174292 q = 0) : d175053 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174292, d175053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15889 q selected
    | true =>
      simp only [d174292, d175053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
  have h2 (q : Pattern) (selected : d174293 q = 0) : d175054 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174293, d175054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174293, d175054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174294 q = 0) : d175055 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174294, d175055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174294, d175055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174299 q = 0) : d175060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174299, d175060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
    | true =>
      simp only [d174299, d175060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15891 q selected
  have h5 (q : Pattern) (selected : d174300 q = 0) : d175061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174300, d175061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174300, d175061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174301 q = 0) : d175062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174301, d175062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174301, d175062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174302 q = 0) : d175063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174302, d175063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174302, d175063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174307 q = 0) : d175068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
    | true =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
  have h9 (q : Pattern) (selected : d174308 q = 0) : d175069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174309 q = 0) : d175070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174315 q = 0) : d175076 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15893 q selected
  have h12 (q : Pattern) (selected : d174316 q = 0) : d175077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174317 q = 0) : d175078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174318 q = 0) : d175079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174319 q = 0) : d175080 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174319, d175080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174319, d175080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d191029 q = 0) : d191599 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191029, d191599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191029, d191599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d191030 q = 0) : d191600 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191030, d191600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191030, d191600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d191031 q = 0) : d191601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191031, d191601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191031, d191601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d191032 q = 0) : d191602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191032, d191602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191032, d191602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d191033 q = 0) : d191603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191033, d191603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d191033, d191603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d191034 q = 0) : d191604 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191034, d191604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191034, d191604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d191035 q = 0) : d191605 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191035, d191605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191035, d191605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d191036 q = 0) : d191606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191036, d191606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d191036, d191606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d191037 q = 0) : d191607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191037, d191607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191037, d191607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d191038 q = 0) : d191608 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191038, d191608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d191038, d191608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d191039 q = 0) : d191609 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191039, d191609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d191039, d191609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d191040 q = 0) : d191610 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191040, d191610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d191040, d191610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro17694 (p : Pattern) (selected : d191045 p = 0) : d191615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174307 q = 0) : d175068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
    | true =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
  have h2 (q : Pattern) (selected : d174308 q = 0) : d175069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174309 q = 0) : d175070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174315 q = 0) : d175076 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15893 q selected
  have h5 (q : Pattern) (selected : d174316 q = 0) : d175077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174317 q = 0) : d175078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174318 q = 0) : d175079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174323 q = 0) : d175084 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174323, d175084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174323, d175084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174324 q = 0) : d175085 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174324, d175085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174324, d175085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d191034 q = 0) : d191604 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191034, d191604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191034, d191604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d191035 q = 0) : d191605 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191035, d191605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191035, d191605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d191036 q = 0) : d191606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191036, d191606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191036, d191606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d191037 q = 0) : d191607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191037, d191607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191037, d191607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d191038 q = 0) : d191608 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191038, d191608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d191038, d191608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d191043 q = 0) : d191613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191043, d191613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d191043, d191613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d191044 q = 0) : d191614 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191044, d191614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d191044, d191614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d191045 q = 0) : d191615 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191045, d191615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d191045, d191615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17695 (p : Pattern) (selected : d191051 p = 0) : d191621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191041 q = 0) : d191611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191041, d191611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17693 q selected
    | true =>
      simp only [d191041, d191611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191042 q = 0) : d191612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191042, d191612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191042, d191612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191046 q = 0) : d191616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191046, d191616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17694 q selected
    | true =>
      simp only [d191046, d191616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191047 q = 0) : d191617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191047, d191617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191047, d191617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191048 q = 0) : d191618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191048, d191618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191048, d191618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191049 q = 0) : d191619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191049, d191619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191049, d191619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191050 q = 0) : d191620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191050, d191620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d191050, d191620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d191051 q = 0) : d191621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191051, d191621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191051, d191621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17696 (p : Pattern) (selected : d191056 p = 0) : d191626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174335 q = 0) : d175096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174335, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174335, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15897 q selected
  have h2 (q : Pattern) (selected : d174336 q = 0) : d175097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174336, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174336, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174337 q = 0) : d175098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174337, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174337, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174338 q = 0) : d175099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174338, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174338, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174339 q = 0) : d175100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174339, d175100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174339, d175100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191052 q = 0) : d191622 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191052, d191622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191052, d191622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191053 q = 0) : d191623 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191053, d191623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191053, d191623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d191054 q = 0) : d191624 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191054, d191624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191054, d191624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d191055 q = 0) : d191625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191055, d191625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191055, d191625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d191056 q = 0) : d191626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191056, d191626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191056, d191626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17697 (p : Pattern) (selected : d191062 p = 0) : d191632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191046 q = 0) : d191616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191046, d191616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17694 q selected
    | true =>
      simp only [d191046, d191616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191047 q = 0) : d191617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191047, d191617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191047, d191617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191057 q = 0) : d191627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191057, d191627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17696 q selected
    | true =>
      simp only [d191057, d191627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191058 q = 0) : d191628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191058, d191628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191058, d191628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191059 q = 0) : d191629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191059, d191629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191059, d191629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191060 q = 0) : d191630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191060, d191630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191060, d191630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191061 q = 0) : d191631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191061, d191631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d191061, d191631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d191062 q = 0) : d191632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191062, d191632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191062, d191632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17698 (p : Pattern) (selected : d191073 p = 0) : d191635 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174360 q = 0) : d175068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174360, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15900 q selected
    | true =>
      simp only [d174360, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15901 q selected
  have h2 (q : Pattern) (selected : d174361 q = 0) : d175069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174361, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174361, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174362 q = 0) : d175070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174362, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174362, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174368 q = 0) : d175076 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174368, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15901 q selected
    | true =>
      simp only [d174368, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15902 q selected
  have h5 (q : Pattern) (selected : d174369 q = 0) : d175077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174369, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174369, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174370 q = 0) : d175078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174370, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174370, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174371 q = 0) : d175079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174371, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174371, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174375 q = 0) : d175096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174375, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15901 q selected
    | true =>
      simp only [d174375, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15903 q selected
  have h9 (q : Pattern) (selected : d174376 q = 0) : d175097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174376, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174376, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174377 q = 0) : d175098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174377, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174377, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174378 q = 0) : d175099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174378, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174378, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174379 q = 0) : d175109 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174379, d175109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174379, d175109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d191064 q = 0) : d191604 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191064, d191604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191064, d191604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d191065 q = 0) : d191605 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191065, d191605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191065, d191605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d191066 q = 0) : d191606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191066, d191606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191066, d191606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d191067 q = 0) : d191607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191067, d191607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191067, d191607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d191068 q = 0) : d191608 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191068, d191608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d191068, d191608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d191069 q = 0) : d191622 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191069, d191622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191069, d191622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d191070 q = 0) : d191623 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191070, d191623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191070, d191623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d191071 q = 0) : d191624 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191071, d191624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d191071, d191624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d191072 q = 0) : d191634 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191072, d191634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d191072, d191634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d191073 q = 0) : d191635 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191073, d191635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d191073, d191635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro17699 (p : Pattern) (selected : d191077 p = 0) : d191626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174375 q = 0) : d175096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174375, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15901 q selected
    | true =>
      simp only [d174375, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15903 q selected
  have h2 (q : Pattern) (selected : d174376 q = 0) : d175097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174376, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174376, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174377 q = 0) : d175098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174377, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174377, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174378 q = 0) : d175099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174378, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174378, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174383 q = 0) : d175100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174383, d175100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174383, d175100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191069 q = 0) : d191622 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191069, d191622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191069, d191622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191070 q = 0) : d191623 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191070, d191623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191070, d191623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d191071 q = 0) : d191624 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191071, d191624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191071, d191624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d191076 q = 0) : d191625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191076, d191625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191076, d191625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d191077 q = 0) : d191626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191077, d191626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191077, d191626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17700 (p : Pattern) (selected : d191083 p = 0) : d191641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191074 q = 0) : d191636 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191074, d191636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17698 q selected
    | true =>
      simp only [d191074, d191636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191075 q = 0) : d191637 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191075, d191637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191075, d191637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191078 q = 0) : d191627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191078, d191627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17699 q selected
    | true =>
      simp only [d191078, d191627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191079 q = 0) : d191628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191079, d191628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191079, d191628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191080 q = 0) : d191638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191080, d191638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191080, d191638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191081 q = 0) : d191639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191081, d191639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191081, d191639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191082 q = 0) : d191640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191082, d191640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d191082, d191640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d191083 q = 0) : d191641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191083, d191641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191083, d191641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17701 (p : Pattern) (selected : d191087 p = 0) : d191645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191078 q = 0) : d191627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191078, d191627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17699 q selected
    | true =>
      simp only [d191078, d191627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191079 q = 0) : d191628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191079, d191628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191079, d191628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191084 q = 0) : d191642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191084, d191642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191084, d191642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191085 q = 0) : d191643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191085, d191643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191085, d191643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191086 q = 0) : d191644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191086, d191644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191086, d191644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191087 q = 0) : d191645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191087, d191645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191087, d191645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17702 (p : Pattern) (selected : d191094 p = 0) : d191652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174307 q = 0) : d175068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
    | true =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
  have h2 (q : Pattern) (selected : d174308 q = 0) : d175069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174309 q = 0) : d175070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174315 q = 0) : d175076 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15893 q selected
  have h5 (q : Pattern) (selected : d174316 q = 0) : d175077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174317 q = 0) : d175078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174318 q = 0) : d175079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174398 q = 0) : d175124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174398, d175124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174398, d175124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15908 q selected
  have h9 (q : Pattern) (selected : d174399 q = 0) : d175125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174399, d175125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174399, d175125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174400 q = 0) : d175126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174400, d175126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174400, d175126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174401 q = 0) : d175127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174401, d175127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174401, d175127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174402 q = 0) : d175128 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174402, d175128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174402, d175128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d191034 q = 0) : d191604 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191034, d191604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191034, d191604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d191035 q = 0) : d191605 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191035, d191605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191035, d191605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d191036 q = 0) : d191606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191036, d191606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191036, d191606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d191037 q = 0) : d191607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191037, d191607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191037, d191607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d191038 q = 0) : d191608 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191038, d191608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d191038, d191608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d191090 q = 0) : d191648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191090, d191648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191090, d191648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d191091 q = 0) : d191649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191091, d191649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191091, d191649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d191092 q = 0) : d191650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191092, d191650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d191092, d191650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d191093 q = 0) : d191651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191093, d191651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d191093, d191651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d191094 q = 0) : d191652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191094, d191652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d191094, d191652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro17703 (p : Pattern) (selected : d191100 p = 0) : d191658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191095 q = 0) : d191653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191095, d191653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17702 q selected
    | true =>
      simp only [d191095, d191653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191096 q = 0) : d191654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191096, d191654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191096, d191654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191097 q = 0) : d191655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191097, d191655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191097, d191655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191098 q = 0) : d191656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191098, d191656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191098, d191656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191099 q = 0) : d191657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191099, d191657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191099, d191657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191100 q = 0) : d191658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191100, d191658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191100, d191658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17704 (p : Pattern) (selected : d191106 p = 0) : d191664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191063 q = 0) : d191633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191063, d191633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17695 q selected
    | true =>
      simp only [d191063, d191633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17697 q selected
  have h2 (q : Pattern) (selected : d191088 q = 0) : d191646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191088, d191646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17700 q selected
    | true =>
      simp only [d191088, d191646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17701 q selected
  have h3 (q : Pattern) (selected : d191089 q = 0) : d191647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191089, d191647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191089, d191647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191101 q = 0) : d191659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191101, d191659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17703 q selected
    | true =>
      simp only [d191101, d191659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191102 q = 0) : d191660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191102, d191660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191102, d191660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191103 q = 0) : d191661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191103, d191661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191103, d191661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d191104 q = 0) : d191662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191104, d191662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191104, d191662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d191105 q = 0) : d191663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191105, d191663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191105, d191663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d191106 q = 0) : d191664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191106, d191664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191106, d191664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17705 (p : Pattern) (selected : d191111 p = 0) : d191645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191057 q = 0) : d191627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191057, d191627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17696 q selected
    | true =>
      simp only [d191057, d191627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191058 q = 0) : d191628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191058, d191628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191058, d191628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191108 q = 0) : d191642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191108, d191642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191108, d191642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191109 q = 0) : d191643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191109, d191643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191109, d191643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191110 q = 0) : d191644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191110, d191644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191110, d191644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191111 q = 0) : d191645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191111, d191645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191111, d191645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17706 (p : Pattern) (selected : d191117 p = 0) : d191671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191112 q = 0) : d191666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191112, d191666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17705 q selected
    | true =>
      simp only [d191112, d191666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191113 q = 0) : d191667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191113, d191667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191113, d191667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191114 q = 0) : d191668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191114, d191668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191114, d191668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191115 q = 0) : d191669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191115, d191669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191115, d191669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191116 q = 0) : d191670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191116, d191670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191116, d191670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191117 q = 0) : d191671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191117, d191671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191117, d191671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17707 (p : Pattern) (selected : d191123 p = 0) : d191677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191107 q = 0) : d191665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191107, d191665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191107, d191665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17704 q selected
  have h2 (q : Pattern) (selected : d191118 q = 0) : d191672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191118, d191672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191118, d191672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17706 q selected
  have h3 (q : Pattern) (selected : d191119 q = 0) : d191673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191119, d191673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191119, d191673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191120 q = 0) : d191674 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191120, d191674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191120, d191674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191121 q = 0) : d191675 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191121, d191675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191121, d191675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191122 q = 0) : d191676 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191122, d191676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191122, d191676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191123 q = 0) : d191677 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191123, d191677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191123, d191677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17708 (p : Pattern) (selected : d191129 p = 0) : d191683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191124 q = 0) : d191678 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191124, d191678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191124, d191678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17707 q selected
  have h2 (q : Pattern) (selected : d191125 q = 0) : d191679 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191125, d191679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191125, d191679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191126 q = 0) : d191680 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191126, d191680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191126, d191680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191127 q = 0) : d191681 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191127, d191681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191127, d191681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191128 q = 0) : d191682 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191128, d191682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191128, d191682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191129 q = 0) : d191683 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191129, d191683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191129, d191683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17709 (p : Pattern) (selected : d191145 p = 0) : d191699 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174455 q = 0) : d175177 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174455, d175177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15916 q selected
    | true =>
      simp only [d174455, d175177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
  have h2 (q : Pattern) (selected : d174456 q = 0) : d175178 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174456, d175178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174456, d175178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174457 q = 0) : d175179 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174457, d175179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174457, d175179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174460 q = 0) : d175182 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174460, d175182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
    | true =>
      simp only [d174460, d175182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15918 q selected
  have h5 (q : Pattern) (selected : d174461 q = 0) : d175183 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174461, d175183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174461, d175183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174462 q = 0) : d175184 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174462, d175184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174462, d175184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174463 q = 0) : d175185 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174463, d175185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174463, d175185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174468 q = 0) : d175190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
    | true =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
  have h9 (q : Pattern) (selected : d174469 q = 0) : d175191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174470 q = 0) : d175192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174476 q = 0) : d175198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15920 q selected
  have h12 (q : Pattern) (selected : d174477 q = 0) : d175199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174478 q = 0) : d175200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174479 q = 0) : d175201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174480 q = 0) : d175202 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174480, d175202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174480, d175202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d191134 q = 0) : d191688 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191134, d191688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191134, d191688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d191135 q = 0) : d191689 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191135, d191689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191135, d191689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d191136 q = 0) : d191690 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191136, d191690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191136, d191690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d191137 q = 0) : d191691 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191137, d191691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191137, d191691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d191138 q = 0) : d191692 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191138, d191692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d191138, d191692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d191139 q = 0) : d191693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191139, d191693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191139, d191693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d191140 q = 0) : d191694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191140, d191694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191140, d191694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d191141 q = 0) : d191695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191141, d191695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d191141, d191695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d191142 q = 0) : d191696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191142, d191696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191142, d191696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d191143 q = 0) : d191697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191143, d191697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d191143, d191697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d191144 q = 0) : d191698 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191144, d191698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d191144, d191698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d191145 q = 0) : d191699 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191145, d191699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d191145, d191699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro17710 (p : Pattern) (selected : d191150 p = 0) : d191704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174468 q = 0) : d175190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
    | true =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
  have h2 (q : Pattern) (selected : d174469 q = 0) : d175191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174470 q = 0) : d175192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174476 q = 0) : d175198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15920 q selected
  have h5 (q : Pattern) (selected : d174477 q = 0) : d175199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174478 q = 0) : d175200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174479 q = 0) : d175201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174484 q = 0) : d175206 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174484, d175206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174484, d175206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174485 q = 0) : d175207 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174485, d175207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174485, d175207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d191139 q = 0) : d191693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191139, d191693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191139, d191693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d191140 q = 0) : d191694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191140, d191694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191140, d191694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d191141 q = 0) : d191695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191141, d191695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191141, d191695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d191142 q = 0) : d191696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191142, d191696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191142, d191696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d191143 q = 0) : d191697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191143, d191697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d191143, d191697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d191148 q = 0) : d191702 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191148, d191702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d191148, d191702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d191149 q = 0) : d191703 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191149, d191703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d191149, d191703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d191150 q = 0) : d191704 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191150, d191704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d191150, d191704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17711 (p : Pattern) (selected : d191156 p = 0) : d191710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191146 q = 0) : d191700 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191146, d191700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17709 q selected
    | true =>
      simp only [d191146, d191700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191147 q = 0) : d191701 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191147, d191701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191147, d191701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191151 q = 0) : d191705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191151, d191705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17710 q selected
    | true =>
      simp only [d191151, d191705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191152 q = 0) : d191706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191152, d191706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191152, d191706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191153 q = 0) : d191707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191153, d191707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191153, d191707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191154 q = 0) : d191708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191154, d191708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191154, d191708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191155 q = 0) : d191709 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191155, d191709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d191155, d191709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d191156 q = 0) : d191710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191156, d191710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191156, d191710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17712 (p : Pattern) (selected : d191161 p = 0) : d191715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174496 q = 0) : d175218 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174496, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174496, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15924 q selected
  have h2 (q : Pattern) (selected : d174497 q = 0) : d175219 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174497, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174497, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174498 q = 0) : d175220 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174498, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174498, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174499 q = 0) : d175221 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174499, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174499, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174500 q = 0) : d175222 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174500, d175222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174500, d175222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191157 q = 0) : d191711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191157, d191711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191157, d191711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191158 q = 0) : d191712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191158, d191712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191158, d191712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d191159 q = 0) : d191713 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191159, d191713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191159, d191713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d191160 q = 0) : d191714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191160, d191714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191160, d191714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d191161 q = 0) : d191715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191161, d191715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191161, d191715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17713 (p : Pattern) (selected : d191167 p = 0) : d191721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191151 q = 0) : d191705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191151, d191705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17710 q selected
    | true =>
      simp only [d191151, d191705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191152 q = 0) : d191706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191152, d191706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191152, d191706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191162 q = 0) : d191716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191162, d191716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17712 q selected
    | true =>
      simp only [d191162, d191716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191163 q = 0) : d191717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191163, d191717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191163, d191717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191164 q = 0) : d191718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191164, d191718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191164, d191718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191165 q = 0) : d191719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191165, d191719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191165, d191719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191166 q = 0) : d191720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191166, d191720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d191166, d191720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d191167 q = 0) : d191721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191167, d191721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191167, d191721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17714 (p : Pattern) (selected : d191178 p = 0) : d191724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174521 q = 0) : d175190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174521, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15927 q selected
    | true =>
      simp only [d174521, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15928 q selected
  have h2 (q : Pattern) (selected : d174522 q = 0) : d175191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174522, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174522, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174523 q = 0) : d175192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174523, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174523, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174529 q = 0) : d175198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174529, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15928 q selected
    | true =>
      simp only [d174529, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15929 q selected
  have h5 (q : Pattern) (selected : d174530 q = 0) : d175199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174530, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174530, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174531 q = 0) : d175200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174531, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174531, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174532 q = 0) : d175201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174532, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174532, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174536 q = 0) : d175218 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174536, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15928 q selected
    | true =>
      simp only [d174536, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15930 q selected
  have h9 (q : Pattern) (selected : d174537 q = 0) : d175219 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174537, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174537, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174538 q = 0) : d175220 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174538, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174538, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174539 q = 0) : d175221 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174539, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174539, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174540 q = 0) : d175231 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174540, d175231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174540, d175231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d191169 q = 0) : d191693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191169, d191693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191169, d191693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d191170 q = 0) : d191694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191170, d191694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191170, d191694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d191171 q = 0) : d191695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191171, d191695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191171, d191695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d191172 q = 0) : d191696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191172, d191696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191172, d191696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d191173 q = 0) : d191697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191173, d191697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d191173, d191697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d191174 q = 0) : d191711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191174, d191711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191174, d191711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d191175 q = 0) : d191712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191175, d191712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191175, d191712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d191176 q = 0) : d191713 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191176, d191713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d191176, d191713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d191177 q = 0) : d191723 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191177, d191723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d191177, d191723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d191178 q = 0) : d191724 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191178, d191724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d191178, d191724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro17715 (p : Pattern) (selected : d191182 p = 0) : d191715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174536 q = 0) : d175218 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174536, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15928 q selected
    | true =>
      simp only [d174536, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15930 q selected
  have h2 (q : Pattern) (selected : d174537 q = 0) : d175219 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174537, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174537, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174538 q = 0) : d175220 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174538, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174538, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174539 q = 0) : d175221 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174539, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174539, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174544 q = 0) : d175222 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174544, d175222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174544, d175222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191174 q = 0) : d191711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191174, d191711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191174, d191711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191175 q = 0) : d191712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191175, d191712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191175, d191712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d191176 q = 0) : d191713 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191176, d191713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191176, d191713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d191181 q = 0) : d191714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191181, d191714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191181, d191714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d191182 q = 0) : d191715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191182, d191715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191182, d191715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17716 (p : Pattern) (selected : d191188 p = 0) : d191730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191179 q = 0) : d191725 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191179, d191725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17714 q selected
    | true =>
      simp only [d191179, d191725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191180 q = 0) : d191726 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191180, d191726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191180, d191726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191183 q = 0) : d191716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191183, d191716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17715 q selected
    | true =>
      simp only [d191183, d191716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191184 q = 0) : d191717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191184, d191717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191184, d191717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191185 q = 0) : d191727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191185, d191727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191185, d191727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191186 q = 0) : d191728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191186, d191728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191186, d191728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191187 q = 0) : d191729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191187, d191729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d191187, d191729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d191188 q = 0) : d191730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191188, d191730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191188, d191730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17717 (p : Pattern) (selected : d191192 p = 0) : d191734 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191183 q = 0) : d191716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191183, d191716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17715 q selected
    | true =>
      simp only [d191183, d191716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191184 q = 0) : d191717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191184, d191717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191184, d191717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191189 q = 0) : d191731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191189, d191731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191189, d191731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191190 q = 0) : d191732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191190, d191732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191190, d191732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191191 q = 0) : d191733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191191, d191733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191191, d191733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191192 q = 0) : d191734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191192, d191734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191192, d191734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17718 (p : Pattern) (selected : d191199 p = 0) : d191741 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174468 q = 0) : d175190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
    | true =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
  have h2 (q : Pattern) (selected : d174469 q = 0) : d175191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174470 q = 0) : d175192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174476 q = 0) : d175198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15920 q selected
  have h5 (q : Pattern) (selected : d174477 q = 0) : d175199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174478 q = 0) : d175200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174479 q = 0) : d175201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174559 q = 0) : d175246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174559, d175246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174559, d175246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15935 q selected
  have h9 (q : Pattern) (selected : d174560 q = 0) : d175247 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174560, d175247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174560, d175247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174561 q = 0) : d175248 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174561, d175248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174561, d175248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174562 q = 0) : d175249 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174562, d175249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174562, d175249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174563 q = 0) : d175250 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174563, d175250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174563, d175250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d191139 q = 0) : d191693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191139, d191693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191139, d191693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d191140 q = 0) : d191694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191140, d191694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191140, d191694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d191141 q = 0) : d191695 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191141, d191695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191141, d191695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d191142 q = 0) : d191696 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191142, d191696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191142, d191696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d191143 q = 0) : d191697 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191143, d191697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d191143, d191697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d191195 q = 0) : d191737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191195, d191737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d191195, d191737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d191196 q = 0) : d191738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191196, d191738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191196, d191738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d191197 q = 0) : d191739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191197, d191739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d191197, d191739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d191198 q = 0) : d191740 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191198, d191740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d191198, d191740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d191199 q = 0) : d191741 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191199, d191741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d191199, d191741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro17719 (p : Pattern) (selected : d191205 p = 0) : d191747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191200 q = 0) : d191742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191200, d191742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17718 q selected
    | true =>
      simp only [d191200, d191742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191201 q = 0) : d191743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191201, d191743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191201, d191743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191202 q = 0) : d191744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191202, d191744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191202, d191744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191203 q = 0) : d191745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191203, d191745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191203, d191745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191204 q = 0) : d191746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191204, d191746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191204, d191746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191205 q = 0) : d191747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191205, d191747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191205, d191747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17720 (p : Pattern) (selected : d191211 p = 0) : d191753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191168 q = 0) : d191722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191168, d191722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17711 q selected
    | true =>
      simp only [d191168, d191722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17713 q selected
  have h2 (q : Pattern) (selected : d191193 q = 0) : d191735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191193, d191735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17716 q selected
    | true =>
      simp only [d191193, d191735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17717 q selected
  have h3 (q : Pattern) (selected : d191194 q = 0) : d191736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191194, d191736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191194, d191736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191206 q = 0) : d191748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191206, d191748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17719 q selected
    | true =>
      simp only [d191206, d191748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191207 q = 0) : d191749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191207, d191749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191207, d191749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191208 q = 0) : d191750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191208, d191750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191208, d191750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d191209 q = 0) : d191751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191209, d191751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191209, d191751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d191210 q = 0) : d191752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191210, d191752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191210, d191752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d191211 q = 0) : d191753 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191211, d191753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191211, d191753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17721 (p : Pattern) (selected : d191216 p = 0) : d191734 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191162 q = 0) : d191716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191162, d191716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17712 q selected
    | true =>
      simp only [d191162, d191716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191163 q = 0) : d191717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191163, d191717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191163, d191717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191213 q = 0) : d191731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191213, d191731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191213, d191731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191214 q = 0) : d191732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191214, d191732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191214, d191732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191215 q = 0) : d191733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191215, d191733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191215, d191733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191216 q = 0) : d191734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191216, d191734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191216, d191734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17722 (p : Pattern) (selected : d191222 p = 0) : d191760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191217 q = 0) : d191755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191217, d191755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17721 q selected
    | true =>
      simp only [d191217, d191755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191218 q = 0) : d191756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191218, d191756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191218, d191756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191219 q = 0) : d191757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191219, d191757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191219, d191757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191220 q = 0) : d191758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191220, d191758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191220, d191758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191221 q = 0) : d191759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191221, d191759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191221, d191759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191222 q = 0) : d191760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191222, d191760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191222, d191760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17723 (p : Pattern) (selected : d191228 p = 0) : d191766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191212 q = 0) : d191754 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191212, d191754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191212, d191754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17720 q selected
  have h2 (q : Pattern) (selected : d191223 q = 0) : d191761 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191223, d191761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191223, d191761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17722 q selected
  have h3 (q : Pattern) (selected : d191224 q = 0) : d191762 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191224, d191762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191224, d191762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191225 q = 0) : d191763 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191225, d191763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191225, d191763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191226 q = 0) : d191764 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191226, d191764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191226, d191764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191227 q = 0) : d191765 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191227, d191765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191227, d191765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d191228 q = 0) : d191766 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191228, d191766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191228, d191766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17724 (p : Pattern) (selected : d191234 p = 0) : d191772 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191229 q = 0) : d191767 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191229, d191767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191229, d191767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17723 q selected
  have h2 (q : Pattern) (selected : d191230 q = 0) : d191768 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191230, d191768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191230, d191768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d191231 q = 0) : d191769 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191231, d191769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191231, d191769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191232 q = 0) : d191770 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191232, d191770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191232, d191770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d191233 q = 0) : d191771 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191233, d191771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191233, d191771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191234 q = 0) : d191772 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191234, d191772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d191234, d191772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17725 (p : Pattern) (selected : d191240 p = 0) : d191778 p = 1 := by
  have h0 (q : Pattern) (selected : d190833 q = 0) : d191441 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d190833, d191441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17646 q selected
    | true =>
      simp only [d190833, d191441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17661 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d190923 q = 0) : d191509 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d190923, d191509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190923, d191509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17676 q selected
  have h3 (q : Pattern) (selected : d190924 q = 0) : d191510 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d190924, d191510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190924, d191510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d191026 q = 0) : d191596 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d191026, d191596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191026, d191596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17692 q selected
  have h5 (q : Pattern) (selected : d191027 q = 0) : d191597 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d191027, d191597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191027, d191597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d191028 q = 0) : d191598 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d191028, d191598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191028, d191598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d191130 q = 0) : d191684 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d191130, d191684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191130, d191684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17708 q selected
  have h8 (q : Pattern) (selected : d191131 q = 0) : d191685 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d191131, d191685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191131, d191685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d191132 q = 0) : d191686 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d191132, d191686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191132, d191686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d191133 q = 0) : d191687 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d191133, d191687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d191133, d191687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d191235 q = 0) : d191773 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d191235, d191773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191235, d191773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17724 q selected
  have h12 (q : Pattern) (selected : d191236 q = 0) : d191774 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d191236, d191774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191236, d191774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d191237 q = 0) : d191775 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d191237, d191775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191237, d191775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d191238 q = 0) : d191776 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d191238, d191776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191238, d191776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d191239 q = 0) : d191777 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d191239, d191777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d191239, d191777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d191240 q = 0) : d191778 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d191240, d191778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d191240, d191778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro17726 (p : Pattern) (selected : d191246 p = 0) : d191784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191241 q = 0) : d191779 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d191241, d191779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17725 q selected
    | true =>
      simp only [d191241, d191779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191242 q = 0) : d191780 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d191242, d191780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191242, d191780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d191243 q = 0) : d191781 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d191243, d191781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191243, d191781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191244 q = 0) : d191782 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d191244, d191782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191244, d191782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191245 q = 0) : d191783 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d191245, d191783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191245, d191783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191246 q = 0) : d191784 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d191246, d191784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191246, d191784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17727 (p : Pattern) (selected : d191252 p = 0) : d191790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191247 q = 0) : d191785 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d191247, d191785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17726 q selected
    | true =>
      simp only [d191247, d191785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191248 q = 0) : d191786 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d191248, d191786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191248, d191786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d191249 q = 0) : d191787 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d191249, d191787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191249, d191787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191250 q = 0) : d191788 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d191250, d191788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191250, d191788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191251 q = 0) : d191789 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d191251, d191789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191251, d191789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191252 q = 0) : d191790 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d191252, d191790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191252, d191790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17728 (p : Pattern) (selected : d191258 p = 0) : d191796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191253 q = 0) : d191791 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d191253, d191791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17727 q selected
    | true =>
      simp only [d191253, d191791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191254 q = 0) : d191792 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d191254, d191792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191254, d191792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d191255 q = 0) : d191793 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d191255, d191793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191255, d191793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191256 q = 0) : d191794 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d191256, d191794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191256, d191794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191257 q = 0) : d191795 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d191257, d191795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191257, d191795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191258 q = 0) : d191796 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d191258, d191796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191258, d191796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17729 (p : Pattern) (selected : d191264 p = 0) : d191802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191259 q = 0) : d191797 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d191259, d191797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17728 q selected
    | true =>
      simp only [d191259, d191797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191260 q = 0) : d191798 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d191260, d191798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191260, d191798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d191261 q = 0) : d191799 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d191261, d191799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191261, d191799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191262 q = 0) : d191800 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d191262, d191800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191262, d191800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191263 q = 0) : d191801 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d191263, d191801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191263, d191801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191264 q = 0) : d191802 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d191264, d191802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191264, d191802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17730 (p : Pattern) (selected : d191270 p = 0) : d191808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191265 q = 0) : d191803 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d191265, d191803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17729 q selected
    | true =>
      simp only [d191265, d191803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191266 q = 0) : d191804 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d191266, d191804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191266, d191804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d191267 q = 0) : d191805 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d191267, d191805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191267, d191805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191268 q = 0) : d191806 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d191268, d191806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191268, d191806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191269 q = 0) : d191807 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d191269, d191807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191269, d191807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191270 q = 0) : d191808 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d191270, d191808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191270, d191808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17731 (p : Pattern) (selected : d191276 p = 0) : d191814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191271 q = 0) : d191809 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d191271, d191809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17730 q selected
    | true =>
      simp only [d191271, d191809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191272 q = 0) : d191810 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d191272, d191810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191272, d191810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d191273 q = 0) : d191811 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d191273, d191811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191273, d191811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191274 q = 0) : d191812 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d191274, d191812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191274, d191812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191275 q = 0) : d191813 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d191275, d191813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191275, d191813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191276 q = 0) : d191814 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d191276, d191814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191276, d191814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17732 (p : Pattern) (selected : d191282 p = 0) : d191820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d191277 q = 0) : d191815 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d191277, d191815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17731 q selected
    | true =>
      simp only [d191277, d191815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d191278 q = 0) : d191816 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d191278, d191816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191278, d191816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d191279 q = 0) : d191817 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d191279, d191817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d191279, d191817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d191280 q = 0) : d191818 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d191280, d191818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d191280, d191818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d191281 q = 0) : d191819 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d191281, d191819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d191281, d191819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d191282 q = 0) : d191820 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d191282, d191820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d191282, d191820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17733 (p : Pattern) (selected : d190674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
    | true =>
      simp only [d173806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173810 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190670 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190671 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190673 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190674 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17734 (p : Pattern) (selected : d190680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17733 q selected
    | true =>
      simp only [d190675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190677 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190678 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190679 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190680 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17735 (p : Pattern) (selected : d190686 p = 1) : d192533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190669 q = 1) : d190669 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d190681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17734 q selected
    | true =>
      simp only [d190681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d190682 q = 1) : d192529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190682, d192529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190682, d192529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190643 q = 1) : d190643 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d190683 q = 1) : d192530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190683, d192530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190683, d192530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190684 q = 1) : d192531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190684, d192531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190684, d192531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190685 q = 1) : d192532 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190685, d192532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190685, d192532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190686 q = 1) : d192533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190686, d192533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190686, d192533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17736 (p : Pattern) (selected : d190692 p = 1) : d192539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190687 q = 1) : d192534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190687, d192534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190687, d192534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17735 q selected
  have h2 (q : Pattern) (selected : d190688 q = 1) : d192535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190688, d192535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190688, d192535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d190689 q = 1) : d192536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190689, d192536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190689, d192536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190690 q = 1) : d192537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190690, d192537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190690, d192537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190691 q = 1) : d192538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190691, d192538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190691, d192538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190692 q = 1) : d192539 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190692, d192539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190692, d192539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17737 (p : Pattern) (selected : d190714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15956 q selected
    | true =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
  have h2 (q : Pattern) (selected : d173857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
    | true =>
      simp only [d173806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173859 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173860 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190710 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190711 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190670 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190671 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190712 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190713 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190714 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17738 (p : Pattern) (selected : d190720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190715 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17737 q selected
    | true =>
      simp only [d190715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190716 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17733 q selected
    | true =>
      simp only [d190675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190717 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190718 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190719 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190720 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17739 (p : Pattern) (selected : d190732 p = 1) : d192549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190709 q = 1) : d190709 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d190721 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17738 q selected
    | true =>
      simp only [d190721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17734 q selected
  have h3 (q : Pattern) (selected : d190722 q = 1) : d192545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190722, d192545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190722, d192545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190728 q = 1) : d190728 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d190729 q = 1) : d192546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190729, d192546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190729, d192546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190730 q = 1) : d192547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190730, d192547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190730, d192547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190731 q = 1) : d192548 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190731, d192548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190731, d192548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190732 q = 1) : d192549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190732, d192549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190732, d192549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17740 (p : Pattern) (selected : d190744 p = 1) : d192555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190733 q = 1) : d192550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190733, d192550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190733, d192550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17739 q selected
  have h2 (q : Pattern) (selected : d190739 q = 1) : d190739 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d190740 q = 1) : d192551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190740, d192551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190740, d192551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190741 q = 1) : d192552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190741, d192552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190741, d192552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190742 q = 1) : d192553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190742, d192553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190742, d192553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190743 q = 1) : d192554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190743, d192554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190743, d192554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190744 q = 1) : d192555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190744, d192555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190744, d192555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17741 (p : Pattern) (selected : d190750 p = 1) : d192561 p = 1 := by
  have h0 (q : Pattern) (selected : d190657 q = 1) : d190657 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d190693 q = 1) : d192540 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190693, d192540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190693, d192540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17736 q selected
  have h3 (q : Pattern) (selected : d190694 q = 1) : d192541 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190694, d192541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190694, d192541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190695 q = 1) : d192542 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190695, d192542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190695, d192542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190696 q = 1) : d192543 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190696, d192543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190696, d192543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190697 q = 1) : d192544 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190697, d192544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190697, d192544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190745 q = 1) : d192556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190745, d192556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190745, d192556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17740 q selected
  have h8 (q : Pattern) (selected : d190746 q = 1) : d192557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190746, d192557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190746, d192557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d190747 q = 1) : d192558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190747, d192558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190747, d192558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190748 q = 1) : d192559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190748, d192559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190748, d192559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d190749 q = 1) : d192560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190749, d192560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190749, d192560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190750 q = 1) : d192561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190750, d192561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190750, d192561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro17742 (p : Pattern) (selected : d190783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173939 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15962 q selected
    | true =>
      simp only [d173939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15956 q selected
  have h2 (q : Pattern) (selected : d173940 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173941 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15956 q selected
    | true =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
  have h5 (q : Pattern) (selected : d173857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173942 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173943 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173944 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190778 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190779 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190710 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190711 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190780 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190781 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190782 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190783 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17743 (p : Pattern) (selected : d190787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15956 q selected
    | true =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
  have h2 (q : Pattern) (selected : d173857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173943 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173948 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190710 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190711 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190781 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d190786 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d190786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d190787 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17744 (p : Pattern) (selected : d190793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190784 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17742 q selected
    | true =>
      simp only [d190784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190785 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17743 q selected
    | true =>
      simp only [d190788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d190792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d190793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d190793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17745 (p : Pattern) (selected : d190797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d190788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17743 q selected
    | true =>
      simp only [d190788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d190789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d190789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190794 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d190794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d190794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d190795 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d190795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190796 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d190796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190797 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d190797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17746 (p : Pattern) (selected : d190809 p = 1) : d192566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190777 q = 1) : d190777 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d190798 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d190798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17744 q selected
    | true =>
      simp only [d190798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17745 q selected
  have h3 (q : Pattern) (selected : d190799 q = 1) : d192562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d190799, d192562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190799, d192562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190805 q = 1) : d190805 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d190806 q = 1) : d192563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190806, d192563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190806, d192563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190807 q = 1) : d192564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d190807, d192564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190807, d192564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d190808 q = 1) : d192565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d190808, d192565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190808, d192565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d190809 q = 1) : d192566 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d190809, d192566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190809, d192566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17747 (p : Pattern) (selected : d190826 p = 1) : d192572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190810 q = 1) : d192567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d190810, d192567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190810, d192567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17746 q selected
  have h2 (q : Pattern) (selected : d190821 q = 1) : d190821 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d190822 q = 1) : d192568 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d190822, d192568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190822, d192568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190823 q = 1) : d192569 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d190823, d192569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d190823, d192569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d190824 q = 1) : d192570 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d190824, d192570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190824, d192570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d190825 q = 1) : d192571 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d190825, d192571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190825, d192571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d190826 q = 1) : d192572 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d190826, d192572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190826, d192572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17748 (p : Pattern) (selected : d190832 p = 1) : d192578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d190827 q = 1) : d192573 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d190827, d192573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190827, d192573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17747 q selected
  have h2 (q : Pattern) (selected : d190828 q = 1) : d192574 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d190828, d192574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190828, d192574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d190829 q = 1) : d192575 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d190829, d192575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190829, d192575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d190830 q = 1) : d192576 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d190830, d192576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190830, d192576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d190831 q = 1) : d192577 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d190831, d192577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190831, d192577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d190832 q = 1) : d192578 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d190832, d192578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190832, d192578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17749 (p : Pattern) (selected : d190873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174056 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15970 q selected
    | true =>
      simp only [d174056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15971 q selected
  have h2 (q : Pattern) (selected : d174057 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174058 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174060 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15971 q selected
    | true =>
      simp only [d174060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15972 q selected
  have h5 (q : Pattern) (selected : d174061 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174062 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174063 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174064 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174065 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d190866 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d190866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d190867 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d190868 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d190868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d190868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190869 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d190869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d190869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d190870 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d190870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d190871 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d190871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d190871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d190872 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d190872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d190872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d190873 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d190873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
end NetHack.Soko22Hazard87
