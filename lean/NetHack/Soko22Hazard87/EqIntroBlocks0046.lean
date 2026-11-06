import NetHack.Soko22Hazard87.EqIntroBlocks0045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro11500 (p : Pattern) (selected : d132921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85882 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h2 (q : Pattern) (selected : d85883 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85884 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132920 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132921 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d132921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11501 (p : Pattern) (selected : d132927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132922 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11500 q selected
    | true =>
      simp only [d132922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132923 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132924 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132925 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132926 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d132927 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11502 (p : Pattern) (selected : d132933 p = 1) : d135163 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132919 q = 1) : d132919 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d132928 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11501 q selected
    | true =>
      simp only [d132928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d132929 q = 1) : d135159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132929, d135159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132929, d135159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d132813 q = 1) : d132813 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d132930 q = 1) : d135160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132930, d135160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132930, d135160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132931 q = 1) : d135161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132931, d135161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132931, d135161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132932 q = 1) : d135162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132932, d135162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132932, d135162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132933 q = 1) : d135163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132933, d135163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132933, d135163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11503 (p : Pattern) (selected : d132939 p = 1) : d135169 p = 1 := by
  have h0 (q : Pattern) (selected : d132843 q = 1) : d132843 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132897 q = 1) : d135147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132897, d135147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11496 q selected
    | true =>
      simp only [d132897, d135147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11498 q selected
  have h2 (q : Pattern) (selected : d132899 q = 1) : d132899 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d132900 q = 1) : d135148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132900, d135148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132900, d135148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d132901 q = 1) : d135149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132901, d135149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132901, d135149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132902 q = 1) : d135150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132902, d135150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132902, d135150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132906 q = 1) : d135154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132906, d135154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132906, d135154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11499 q selected
  have h8 (q : Pattern) (selected : d132907 q = 1) : d135155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132907, d135155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132907, d135155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d132908 q = 1) : d135156 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132908, d135156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d132908, d135156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d132909 q = 1) : d135157 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132909, d135157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d132909, d135157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d132910 q = 1) : d135158 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132910, d135158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132910, d135158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d132934 q = 1) : d135164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132934, d135164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132934, d135164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11502 q selected
  have h13 (q : Pattern) (selected : d132935 q = 1) : d135165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132935, d135165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d132935, d135165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d132936 q = 1) : d135166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132936, d135166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d132936, d135166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d132937 q = 1) : d135167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132937, d135167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d132937, d135167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d132938 q = 1) : d135168 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132938, d135168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d132938, d135168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d132939 q = 1) : d135169 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132939, d135169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d132939, d135169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro11504 (p : Pattern) (selected : d132945 p = 1) : d135175 p = 1 := by
  have h0 (q : Pattern) (selected : d132828 q = 1) : d132828 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d132940 q = 1) : d135170 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132940, d135170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132940, d135170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11503 q selected
  have h3 (q : Pattern) (selected : d132941 q = 1) : d135171 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132941, d135171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132941, d135171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d132942 q = 1) : d135172 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132942, d135172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132942, d135172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132943 q = 1) : d135173 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132943, d135173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132943, d135173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132944 q = 1) : d135174 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132944, d135174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132944, d135174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132945 q = 1) : d135175 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132945, d135175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132945, d135175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro11505 (p : Pattern) (selected : d132983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85948 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
  have h2 (q : Pattern) (selected : d85949 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h4 (q : Pattern) (selected : d85824 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85950 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85825 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132982 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132983 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d132983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11506 (p : Pattern) (selected : d132989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132984 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11505 q selected
    | true =>
      simp only [d132984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132985 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132867 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11494 q selected
    | true =>
      simp only [d132867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132868 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132986 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132987 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132988 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d132989 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11507 (p : Pattern) (selected : d133001 p = 1) : d135180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132966 q = 1) : d132966 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d132972 q = 1) : d132972 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d132981 q = 1) : d132981 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d132990 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11506 q selected
    | true =>
      simp only [d132990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11495 q selected
  have h5 (q : Pattern) (selected : d132991 q = 1) : d135176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132991, d135176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132991, d135176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132997 q = 1) : d132997 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d132998 q = 1) : d135177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132998, d135177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132998, d135177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132999 q = 1) : d135178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132999, d135178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132999, d135178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133000 q = 1) : d135179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133000, d135179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133000, d135179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133001 q = 1) : d135180 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133001, d135180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133001, d135180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11508 (p : Pattern) (selected : d133013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132984 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11505 q selected
    | true =>
      simp only [d132984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132985 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132867 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11494 q selected
    | true =>
      simp only [d132867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132868 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132986 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132987 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132988 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133013 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11509 (p : Pattern) (selected : d133022 p = 1) : d135185 p = 1 := by
  have h0 (q : Pattern) (selected : d132966 q = 1) : d132966 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132972 q = 1) : d132972 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d132981 q = 1) : d132981 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d132990 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11506 q selected
    | true =>
      simp only [d132990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11495 q selected
  have h4 (q : Pattern) (selected : d132991 q = 1) : d135176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132991, d135176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132991, d135176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132997 q = 1) : d132997 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d132998 q = 1) : d135177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132998, d135177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132998, d135177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132999 q = 1) : d135178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132999, d135178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132999, d135178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133000 q = 1) : d135179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133000, d135179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133000, d135179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133006 q = 1) : d133006 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d133010 q = 1) : d133010 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d133012 q = 1) : d133012 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d133014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11508 q selected
    | true =>
      simp only [d133014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11497 q selected
  have h13 (q : Pattern) (selected : d133015 q = 1) : d135181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133015, d135181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133015, d135181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133018 q = 1) : d133018 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133019 q = 1) : d135182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133019, d135182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133019, d135182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133020 q = 1) : d135183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133020, d135183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133020, d135183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133021 q = 1) : d135184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133021, d135184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133021, d135184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133022 q = 1) : d135185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133022, d135185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133022, d135185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11510 (p : Pattern) (selected : d133031 p = 1) : d135192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133012 q = 1) : d133012 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11508 q selected
    | true =>
      simp only [d133014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11497 q selected
  have h3 (q : Pattern) (selected : d133015 q = 1) : d135181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133015, d135181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133015, d135181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133018 q = 1) : d133018 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133019 q = 1) : d135182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133019, d135182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133019, d135182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133029 q = 1) : d135190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133029, d135190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133029, d135190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133030 q = 1) : d135191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133030, d135191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133030, d135191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133031 q = 1) : d135192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133031, d135192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133031, d135192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11511 (p : Pattern) (selected : d133049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
  have h2 (q : Pattern) (selected : d86019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85882 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h4 (q : Pattern) (selected : d85883 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85884 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133048 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133049 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11512 (p : Pattern) (selected : d133055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133050 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11511 q selected
    | true =>
      simp only [d133050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133051 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132922 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11500 q selected
    | true =>
      simp only [d132922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132923 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133052 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133053 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133054 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133055 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11513 (p : Pattern) (selected : d133067 p = 1) : d135202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133047 q = 1) : d133047 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11512 q selected
    | true =>
      simp only [d133056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11501 q selected
  have h3 (q : Pattern) (selected : d133057 q = 1) : d135198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133057, d135198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133057, d135198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133063 q = 1) : d133063 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133064 q = 1) : d135199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133064, d135199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133064, d135199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133065 q = 1) : d135200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133065, d135200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133065, d135200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133066 q = 1) : d135201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133066, d135201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133066, d135201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133067 q = 1) : d135202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133067, d135202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133067, d135202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11514 (p : Pattern) (selected : d133079 p = 1) : d135208 p = 1 := by
  have h0 (q : Pattern) (selected : d132960 q = 1) : d132960 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133023 q = 1) : d135186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133023, d135186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11507 q selected
    | true =>
      simp only [d133023, d135186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11509 q selected
  have h2 (q : Pattern) (selected : d133025 q = 1) : d133025 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133026 q = 1) : d135187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133026, d135187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133026, d135187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133027 q = 1) : d135188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133027, d135188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133027, d135188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133028 q = 1) : d135189 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133028, d135189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133028, d135189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133032 q = 1) : d135193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133032, d135193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133032, d135193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11510 q selected
  have h8 (q : Pattern) (selected : d133034 q = 1) : d133034 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d133035 q = 1) : d135194 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133035, d135194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133035, d135194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133036 q = 1) : d135195 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133036, d135195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133036, d135195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d133037 q = 1) : d135196 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133037, d135196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133037, d135196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d133038 q = 1) : d135197 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133038, d135197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133038, d135197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d133068 q = 1) : d135203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133068, d135203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133068, d135203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11513 q selected
  have h14 (q : Pattern) (selected : d133074 q = 1) : d133074 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133075 q = 1) : d135204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133075, d135204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133075, d135204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133076 q = 1) : d135205 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133076, d135205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133076, d135205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d133077 q = 1) : d135206 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133077, d135206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133077, d135206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d133078 q = 1) : d135207 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133078, d135207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133078, d135207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d133079 q = 1) : d135208 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133079, d135208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d133079, d135208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11515 (p : Pattern) (selected : d133085 p = 1) : d135214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133080 q = 1) : d135209 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133080, d135209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133080, d135209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11514 q selected
  have h2 (q : Pattern) (selected : d133081 q = 1) : d135210 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133081, d135210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133081, d135210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133082 q = 1) : d135211 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133082, d135211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133082, d135211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133083 q = 1) : d135212 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133083, d135212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133083, d135212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133084 q = 1) : d135213 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133084, d135213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133084, d135213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133085 q = 1) : d135214 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133085, d135214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133085, d135214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11516 (p : Pattern) (selected : d133149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro54 q selected
  have h2 (q : Pattern) (selected : d86127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86128 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro55 q selected
  have h4 (q : Pattern) (selected : d86129 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86130 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86134 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133148 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133149 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11517 (p : Pattern) (selected : d133153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86128 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro55 q selected
  have h2 (q : Pattern) (selected : d86129 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86134 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133152 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133153 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11518 (p : Pattern) (selected : d133159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133150 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11516 q selected
    | true =>
      simp only [d133150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133151 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11517 q selected
    | true =>
      simp only [d133154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133156 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133157 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133158 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133159 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11519 (p : Pattern) (selected : d133163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11517 q selected
    | true =>
      simp only [d133154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133160 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133161 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133162 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133163 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11520 (p : Pattern) (selected : d133182 p = 1) : d135220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133129 q = 1) : d133129 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133138 q = 1) : d133138 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133147 q = 1) : d133147 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d133164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11518 q selected
    | true =>
      simp only [d133164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11519 q selected
  have h5 (q : Pattern) (selected : d133165 q = 1) : d135216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133165, d135216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133165, d135216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133178 q = 1) : d133178 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d133179 q = 1) : d135217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133179, d135217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133179, d135217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133180 q = 1) : d135218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133180, d135218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133180, d135218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133181 q = 1) : d135219 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133181, d135219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133181, d135219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133182 q = 1) : d135220 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133182, d135220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133182, d135220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11521 (p : Pattern) (selected : d133196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133150 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11516 q selected
    | true =>
      simp only [d133150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133151 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11517 q selected
    | true =>
      simp only [d133154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133156 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133157 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133158 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133196 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11522 (p : Pattern) (selected : d133197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11517 q selected
    | true =>
      simp only [d133154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133160 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133161 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133162 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133197 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11523 (p : Pattern) (selected : d133206 p = 1) : d135225 p = 1 := by
  have h0 (q : Pattern) (selected : d133129 q = 1) : d133129 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133138 q = 1) : d133138 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133147 q = 1) : d133147 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11518 q selected
    | true =>
      simp only [d133164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11519 q selected
  have h4 (q : Pattern) (selected : d133165 q = 1) : d135216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133165, d135216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133165, d135216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133178 q = 1) : d133178 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d133179 q = 1) : d135217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133179, d135217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133179, d135217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133180 q = 1) : d135218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133180, d135218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133180, d135218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133181 q = 1) : d135219 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133181, d135219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133181, d135219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133188 q = 1) : d133188 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d133193 q = 1) : d133193 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d133195 q = 1) : d133195 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d133198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11521 q selected
    | true =>
      simp only [d133198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11522 q selected
  have h13 (q : Pattern) (selected : d133199 q = 1) : d135221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133199, d135221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133199, d135221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133202 q = 1) : d133202 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133203 q = 1) : d135222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133203, d135222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133203, d135222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133204 q = 1) : d135223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133204, d135223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133204, d135223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133205 q = 1) : d135224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133205, d135224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133205, d135224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133206 q = 1) : d135225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133206, d135225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133206, d135225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11524 (p : Pattern) (selected : d133226 p = 1) : d135232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133195 q = 1) : d133195 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11521 q selected
    | true =>
      simp only [d133198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11522 q selected
  have h3 (q : Pattern) (selected : d133199 q = 1) : d135221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133199, d135221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133199, d135221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133202 q = 1) : d133202 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133203 q = 1) : d135222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133203, d135222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133203, d135222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133224 q = 1) : d135230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133224, d135230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133224, d135230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133225 q = 1) : d135231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133225, d135231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133225, d135231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133226 q = 1) : d135232 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133226, d135232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133226, d135232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11525 (p : Pattern) (selected : d133256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
  have h2 (q : Pattern) (selected : d86237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86238 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro67 q selected
  have h4 (q : Pattern) (selected : d86239 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86240 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86244 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133255 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133256 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11526 (p : Pattern) (selected : d133260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86238 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro67 q selected
  have h2 (q : Pattern) (selected : d86239 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86244 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133259 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133260 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11527 (p : Pattern) (selected : d133266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11525 q selected
    | true =>
      simp only [d133257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11526 q selected
    | true =>
      simp only [d133261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11528 (p : Pattern) (selected : d133270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11526 q selected
    | true =>
      simp only [d133261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11529 (p : Pattern) (selected : d133289 p = 1) : d135242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133254 q = 1) : d133254 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11527 q selected
    | true =>
      simp only [d133271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11528 q selected
  have h3 (q : Pattern) (selected : d133272 q = 1) : d135238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133272, d135238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133272, d135238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133285 q = 1) : d133285 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133286 q = 1) : d135239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133286, d135239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133286, d135239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133287 q = 1) : d135240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133287, d135240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133287, d135240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133288 q = 1) : d135241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133288, d135241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133288, d135241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133289 q = 1) : d135242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133289, d135242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133289, d135242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11530 (p : Pattern) (selected : d133306 p = 1) : d135248 p = 1 := by
  have h0 (q : Pattern) (selected : d133121 q = 1) : d133121 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133207 q = 1) : d135226 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133207, d135226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11520 q selected
    | true =>
      simp only [d133207, d135226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11523 q selected
  have h2 (q : Pattern) (selected : d133220 q = 1) : d133220 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133221 q = 1) : d135227 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133221, d135227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133221, d135227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133222 q = 1) : d135228 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133222, d135228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133222, d135228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133223 q = 1) : d135229 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133223, d135229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133223, d135229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133227 q = 1) : d135233 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133227, d135233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133227, d135233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11524 q selected
  have h8 (q : Pattern) (selected : d133229 q = 1) : d133229 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d133230 q = 1) : d135234 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133230, d135234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133230, d135234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133231 q = 1) : d135235 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133231, d135235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133231, d135235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d133232 q = 1) : d135236 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133232, d135236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133232, d135236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d133233 q = 1) : d135237 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133233, d135237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133233, d135237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d133290 q = 1) : d135243 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133290, d135243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133290, d135243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11529 q selected
  have h14 (q : Pattern) (selected : d133301 q = 1) : d133301 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133302 q = 1) : d135244 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133302, d135244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133302, d135244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133303 q = 1) : d135245 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133303, d135245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133303, d135245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d133304 q = 1) : d135246 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133304, d135246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133304, d135246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d133305 q = 1) : d135247 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133305, d135247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133305, d135247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d133306 q = 1) : d135248 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133306, d135248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d133306, d135248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11531 (p : Pattern) (selected : d133312 p = 1) : d135254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133307 q = 1) : d135249 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133307, d135249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133307, d135249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11530 q selected
  have h2 (q : Pattern) (selected : d133308 q = 1) : d135250 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133308, d135250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133308, d135250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133309 q = 1) : d135251 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133309, d135251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133309, d135251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133310 q = 1) : d135252 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133310, d135252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133310, d135252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133311 q = 1) : d135253 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133311, d135253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133311, d135253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133312 q = 1) : d135254 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133312, d135254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133312, d135254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11532 (p : Pattern) (selected : d133377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86360 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro83 q selected
  have h2 (q : Pattern) (selected : d86361 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro85 q selected
  have h4 (q : Pattern) (selected : d86363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133377 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11533 (p : Pattern) (selected : d133381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro85 q selected
  have h2 (q : Pattern) (selected : d86363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133380 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133381 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11534 (p : Pattern) (selected : d133387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133378 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11532 q selected
    | true =>
      simp only [d133378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133379 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133382 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11533 q selected
    | true =>
      simp only [d133382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133383 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133384 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133385 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133386 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133387 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11535 (p : Pattern) (selected : d133391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133382 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11533 q selected
    | true =>
      simp only [d133382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133383 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133388 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133390 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133391 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11536 (p : Pattern) (selected : d133410 p = 1) : d135261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133357 q = 1) : d133357 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133366 q = 1) : d133366 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133375 q = 1) : d133375 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d133392 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11534 q selected
    | true =>
      simp only [d133392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11535 q selected
  have h5 (q : Pattern) (selected : d133393 q = 1) : d135257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133393, d135257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133393, d135257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133406 q = 1) : d133406 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d133407 q = 1) : d135258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133407, d135258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133407, d135258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133408 q = 1) : d135259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133408, d135259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133408, d135259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133409 q = 1) : d135260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133409, d135260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133409, d135260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133410 q = 1) : d135261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133410, d135261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133410, d135261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11537 (p : Pattern) (selected : d133424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133378 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11532 q selected
    | true =>
      simp only [d133378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133379 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133382 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11533 q selected
    | true =>
      simp only [d133382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133383 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133384 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133385 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133386 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133424 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11538 (p : Pattern) (selected : d133425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133382 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11533 q selected
    | true =>
      simp only [d133382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133383 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133388 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133390 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133425 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11539 (p : Pattern) (selected : d133434 p = 1) : d135266 p = 1 := by
  have h0 (q : Pattern) (selected : d133357 q = 1) : d133357 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133366 q = 1) : d133366 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133375 q = 1) : d133375 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133392 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11534 q selected
    | true =>
      simp only [d133392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11535 q selected
  have h4 (q : Pattern) (selected : d133393 q = 1) : d135257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133393, d135257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133393, d135257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133406 q = 1) : d133406 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d133407 q = 1) : d135258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133407, d135258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133407, d135258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133408 q = 1) : d135259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133408, d135259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133408, d135259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133409 q = 1) : d135260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133409, d135260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133409, d135260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133416 q = 1) : d133416 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d133421 q = 1) : d133421 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d133423 q = 1) : d133423 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d133426 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11537 q selected
    | true =>
      simp only [d133426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11538 q selected
  have h13 (q : Pattern) (selected : d133427 q = 1) : d135262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133427, d135262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133427, d135262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133430 q = 1) : d133430 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133431 q = 1) : d135263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133431, d135263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133431, d135263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133432 q = 1) : d135264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133432, d135264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133432, d135264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133433 q = 1) : d135265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133433, d135265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133433, d135265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133434 q = 1) : d135266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133434, d135266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133434, d135266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11540 (p : Pattern) (selected : d133454 p = 1) : d135273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133423 q = 1) : d133423 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133426 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11537 q selected
    | true =>
      simp only [d133426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11538 q selected
  have h3 (q : Pattern) (selected : d133427 q = 1) : d135262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133427, d135262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133427, d135262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133430 q = 1) : d133430 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133431 q = 1) : d135263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133431, d135263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133431, d135263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133452 q = 1) : d135271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133452, d135271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133452, d135271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133453 q = 1) : d135272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133453, d135272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133453, d135272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133454 q = 1) : d135273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133454, d135273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133454, d135273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11541 (p : Pattern) (selected : d133484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86470 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro96 q selected
  have h2 (q : Pattern) (selected : d86471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86472 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro97 q selected
  have h4 (q : Pattern) (selected : d86473 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86474 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86478 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133483 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133484 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11542 (p : Pattern) (selected : d133488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86472 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro97 q selected
  have h2 (q : Pattern) (selected : d86473 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86478 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133487 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133488 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11543 (p : Pattern) (selected : d133494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11541 q selected
    | true =>
      simp only [d133485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11542 q selected
    | true =>
      simp only [d133489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133491 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133492 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133493 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133494 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11544 (p : Pattern) (selected : d133498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133489 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11542 q selected
    | true =>
      simp only [d133489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133490 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133496 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133497 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133498 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11545 (p : Pattern) (selected : d133517 p = 1) : d135283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133482 q = 1) : d133482 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11543 q selected
    | true =>
      simp only [d133499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11544 q selected
  have h3 (q : Pattern) (selected : d133500 q = 1) : d135279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133500, d135279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133500, d135279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133513 q = 1) : d133513 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133514 q = 1) : d135280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133514, d135280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133514, d135280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133515 q = 1) : d135281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133515, d135281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133515, d135281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133516 q = 1) : d135282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133516, d135282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133516, d135282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133517 q = 1) : d135283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133517, d135283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133517, d135283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11546 (p : Pattern) (selected : d133534 p = 1) : d135289 p = 1 := by
  have h0 (q : Pattern) (selected : d133349 q = 1) : d133349 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133435 q = 1) : d135267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133435, d135267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11536 q selected
    | true =>
      simp only [d133435, d135267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11539 q selected
  have h2 (q : Pattern) (selected : d133448 q = 1) : d133448 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133449 q = 1) : d135268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133449, d135268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133449, d135268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133450 q = 1) : d135269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133450, d135269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133450, d135269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133451 q = 1) : d135270 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133451, d135270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133451, d135270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133455 q = 1) : d135274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133455, d135274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133455, d135274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11540 q selected
  have h8 (q : Pattern) (selected : d133457 q = 1) : d133457 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d133458 q = 1) : d135275 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133458, d135275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133458, d135275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133459 q = 1) : d135276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133459, d135276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133459, d135276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d133460 q = 1) : d135277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133460, d135277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133460, d135277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d133461 q = 1) : d135278 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133461, d135278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133461, d135278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d133518 q = 1) : d135284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133518, d135284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133518, d135284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11545 q selected
  have h14 (q : Pattern) (selected : d133529 q = 1) : d133529 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133530 q = 1) : d135285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133530, d135285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133530, d135285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133531 q = 1) : d135286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133531, d135286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133531, d135286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d133532 q = 1) : d135287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133532, d135287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133532, d135287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d133533 q = 1) : d135288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133533, d135288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133533, d135288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d133534 q = 1) : d135289 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133534, d135289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d133534, d135289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11547 (p : Pattern) (selected : d133540 p = 1) : d135295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133535 q = 1) : d135290 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133535, d135290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133535, d135290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11546 q selected
  have h2 (q : Pattern) (selected : d133536 q = 1) : d135291 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133536, d135291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133536, d135291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133537 q = 1) : d135292 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133537, d135292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133537, d135292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133538 q = 1) : d135293 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133538, d135293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133538, d135293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133539 q = 1) : d135294 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133539, d135294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133539, d135294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133540 q = 1) : d135295 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133540, d135295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133540, d135295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11548 (p : Pattern) (selected : d133606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86595 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro119 q selected
  have h2 (q : Pattern) (selected : d86596 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro121 q selected
  have h4 (q : Pattern) (selected : d86598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86599 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86603 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133605 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133606 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11549 (p : Pattern) (selected : d133610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro121 q selected
  have h2 (q : Pattern) (selected : d86598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86603 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133609 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133610 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11550 (p : Pattern) (selected : d133616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11548 q selected
    | true =>
      simp only [d133607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11549 q selected
    | true =>
      simp only [d133611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133615 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133616 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11551 (p : Pattern) (selected : d133620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11549 q selected
    | true =>
      simp only [d133611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133619 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133620 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11552 (p : Pattern) (selected : d133639 p = 1) : d135303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133586 q = 1) : d133586 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133595 q = 1) : d133595 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133604 q = 1) : d133604 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d133621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11550 q selected
    | true =>
      simp only [d133621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11551 q selected
  have h5 (q : Pattern) (selected : d133622 q = 1) : d135299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133622, d135299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133622, d135299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133635 q = 1) : d133635 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d133636 q = 1) : d135300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133636, d135300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133636, d135300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133637 q = 1) : d135301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133637, d135301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133637, d135301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133638 q = 1) : d135302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133638, d135302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133638, d135302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133639 q = 1) : d135303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133639, d135303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133639, d135303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11553 (p : Pattern) (selected : d133653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133607 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11548 q selected
    | true =>
      simp only [d133607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133608 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11549 q selected
    | true =>
      simp only [d133611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133615 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133653 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11554 (p : Pattern) (selected : d133654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11549 q selected
    | true =>
      simp only [d133611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133617 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133618 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133619 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133654 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11555 (p : Pattern) (selected : d133663 p = 1) : d135308 p = 1 := by
  have h0 (q : Pattern) (selected : d133586 q = 1) : d133586 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133595 q = 1) : d133595 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133604 q = 1) : d133604 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11550 q selected
    | true =>
      simp only [d133621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11551 q selected
  have h4 (q : Pattern) (selected : d133622 q = 1) : d135299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133622, d135299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133622, d135299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133635 q = 1) : d133635 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d133636 q = 1) : d135300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133636, d135300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133636, d135300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133637 q = 1) : d135301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133637, d135301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133637, d135301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133638 q = 1) : d135302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133638, d135302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133638, d135302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133645 q = 1) : d133645 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d133650 q = 1) : d133650 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d133652 q = 1) : d133652 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d133655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11553 q selected
    | true =>
      simp only [d133655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11554 q selected
  have h13 (q : Pattern) (selected : d133656 q = 1) : d135304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133656, d135304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133656, d135304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133659 q = 1) : d133659 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133660 q = 1) : d135305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133660, d135305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133660, d135305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133661 q = 1) : d135306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133661, d135306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133661, d135306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133662 q = 1) : d135307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133662, d135307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133662, d135307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133663 q = 1) : d135308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133663, d135308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133663, d135308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11556 (p : Pattern) (selected : d133683 p = 1) : d135315 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133652 q = 1) : d133652 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11553 q selected
    | true =>
      simp only [d133655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11554 q selected
  have h3 (q : Pattern) (selected : d133656 q = 1) : d135304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133656, d135304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133656, d135304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133659 q = 1) : d133659 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133660 q = 1) : d135305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133660, d135305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133660, d135305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133681 q = 1) : d135313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133681, d135313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133681, d135313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133682 q = 1) : d135314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133682, d135314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133682, d135314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133683 q = 1) : d135315 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133683, d135315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133683, d135315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11557 (p : Pattern) (selected : d133713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro132 q selected
  have h2 (q : Pattern) (selected : d86706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86707 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro133 q selected
  have h4 (q : Pattern) (selected : d86708 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133712 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133713 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11558 (p : Pattern) (selected : d133717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86707 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro133 q selected
  have h2 (q : Pattern) (selected : d86708 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133716 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133717 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11559 (p : Pattern) (selected : d133723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133714 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11557 q selected
    | true =>
      simp only [d133714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133715 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133718 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11558 q selected
    | true =>
      simp only [d133718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133719 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133720 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133721 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133722 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133723 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11560 (p : Pattern) (selected : d133727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133718 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11558 q selected
    | true =>
      simp only [d133718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133719 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133725 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133726 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133727 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11561 (p : Pattern) (selected : d133746 p = 1) : d135325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133711 q = 1) : d133711 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11559 q selected
    | true =>
      simp only [d133728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11560 q selected
  have h3 (q : Pattern) (selected : d133729 q = 1) : d135321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133729, d135321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133729, d135321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133742 q = 1) : d133742 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133743 q = 1) : d135322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133743, d135322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133743, d135322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133744 q = 1) : d135323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133744, d135323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133744, d135323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133745 q = 1) : d135324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133745, d135324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133745, d135324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133746 q = 1) : d135325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133746, d135325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133746, d135325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11562 (p : Pattern) (selected : d133763 p = 1) : d135331 p = 1 := by
  have h0 (q : Pattern) (selected : d133578 q = 1) : d133578 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133664 q = 1) : d135309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133664, d135309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11552 q selected
    | true =>
      simp only [d133664, d135309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11555 q selected
  have h2 (q : Pattern) (selected : d133677 q = 1) : d133677 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133678 q = 1) : d135310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133678, d135310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133678, d135310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133679 q = 1) : d135311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133679, d135311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133679, d135311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133680 q = 1) : d135312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133680, d135312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133680, d135312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133684 q = 1) : d135316 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133684, d135316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133684, d135316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11556 q selected
  have h8 (q : Pattern) (selected : d133686 q = 1) : d133686 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d133687 q = 1) : d135317 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133687, d135317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133687, d135317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133688 q = 1) : d135318 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133688, d135318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133688, d135318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d133689 q = 1) : d135319 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133689, d135319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133689, d135319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d133690 q = 1) : d135320 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133690, d135320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133690, d135320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d133747 q = 1) : d135326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133747, d135326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133747, d135326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11561 q selected
  have h14 (q : Pattern) (selected : d133758 q = 1) : d133758 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133759 q = 1) : d135327 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133759, d135327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133759, d135327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133760 q = 1) : d135328 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133760, d135328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133760, d135328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d133761 q = 1) : d135329 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133761, d135329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133761, d135329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d133762 q = 1) : d135330 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133762, d135330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133762, d135330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d133763 q = 1) : d135331 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133763, d135331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d133763, d135331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11563 (p : Pattern) (selected : d133769 p = 1) : d135337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133764 q = 1) : d135332 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133764, d135332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133764, d135332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11562 q selected
  have h2 (q : Pattern) (selected : d133765 q = 1) : d135333 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133765, d135333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133765, d135333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133766 q = 1) : d135334 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133766, d135334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133766, d135334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133767 q = 1) : d135335 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133767, d135335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133767, d135335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133768 q = 1) : d135336 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133768, d135336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133768, d135336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133769 q = 1) : d135337 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133769, d135337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133769, d135337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11564 (p : Pattern) (selected : d133836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro156 q selected
  have h2 (q : Pattern) (selected : d86832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro158 q selected
  have h4 (q : Pattern) (selected : d86834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133835 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133836 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11565 (p : Pattern) (selected : d133840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro158 q selected
  have h2 (q : Pattern) (selected : d86834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133839 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133840 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11566 (p : Pattern) (selected : d133846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11564 q selected
    | true =>
      simp only [d133837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11565 q selected
    | true =>
      simp only [d133841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11567 (p : Pattern) (selected : d133850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11565 q selected
    | true =>
      simp only [d133841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133847 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133848 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133849 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133850 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11568 (p : Pattern) (selected : d133869 p = 1) : d135346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133816 q = 1) : d133816 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133825 q = 1) : d133825 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133834 q = 1) : d133834 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d133851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11566 q selected
    | true =>
      simp only [d133851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11567 q selected
  have h5 (q : Pattern) (selected : d133852 q = 1) : d135342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133852, d135342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133852, d135342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133865 q = 1) : d133865 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d133866 q = 1) : d135343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133866, d135343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133866, d135343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133867 q = 1) : d135344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133867, d135344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133867, d135344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133868 q = 1) : d135345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133868, d135345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133868, d135345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133869 q = 1) : d135346 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133869, d135346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133869, d135346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11569 (p : Pattern) (selected : d133883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11564 q selected
    | true =>
      simp only [d133837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11565 q selected
    | true =>
      simp only [d133841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133883 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11570 (p : Pattern) (selected : d133884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11565 q selected
    | true =>
      simp only [d133841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133847 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133848 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133849 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133884 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11571 (p : Pattern) (selected : d133893 p = 1) : d135351 p = 1 := by
  have h0 (q : Pattern) (selected : d133816 q = 1) : d133816 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133825 q = 1) : d133825 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133834 q = 1) : d133834 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11566 q selected
    | true =>
      simp only [d133851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11567 q selected
  have h4 (q : Pattern) (selected : d133852 q = 1) : d135342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133852, d135342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133852, d135342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133865 q = 1) : d133865 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d133866 q = 1) : d135343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133866, d135343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133866, d135343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133867 q = 1) : d135344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133867, d135344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133867, d135344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133868 q = 1) : d135345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133868, d135345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133868, d135345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133875 q = 1) : d133875 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d133880 q = 1) : d133880 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d133882 q = 1) : d133882 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d133885 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11569 q selected
    | true =>
      simp only [d133885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11570 q selected
  have h13 (q : Pattern) (selected : d133886 q = 1) : d135347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133886, d135347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133886, d135347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133889 q = 1) : d133889 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133890 q = 1) : d135348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133890, d135348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133890, d135348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133891 q = 1) : d135349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133891, d135349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133891, d135349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133892 q = 1) : d135350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133892, d135350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133892, d135350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133893 q = 1) : d135351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133893, d135351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133893, d135351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11572 (p : Pattern) (selected : d133913 p = 1) : d135358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133882 q = 1) : d133882 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133885 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11569 q selected
    | true =>
      simp only [d133885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11570 q selected
  have h3 (q : Pattern) (selected : d133886 q = 1) : d135347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133886, d135347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133886, d135347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133889 q = 1) : d133889 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133890 q = 1) : d135348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133890, d135348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133890, d135348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133911 q = 1) : d135356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133911, d135356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133911, d135356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133912 q = 1) : d135357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133912, d135357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133912, d135357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133913 q = 1) : d135358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133913, d135358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133913, d135358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11573 (p : Pattern) (selected : d133943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86941 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro169 q selected
  have h2 (q : Pattern) (selected : d86942 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro170 q selected
  have h4 (q : Pattern) (selected : d86944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86945 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133942 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133943 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11574 (p : Pattern) (selected : d133947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro170 q selected
  have h2 (q : Pattern) (selected : d86944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133946 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133947 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11575 (p : Pattern) (selected : d133953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133944 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11573 q selected
    | true =>
      simp only [d133944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133945 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11574 q selected
    | true =>
      simp only [d133948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133950 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133951 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133952 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133953 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11576 (p : Pattern) (selected : d133957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11574 q selected
    | true =>
      simp only [d133948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133954 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11577 (p : Pattern) (selected : d133976 p = 1) : d135368 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133941 q = 1) : d133941 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133958 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11575 q selected
    | true =>
      simp only [d133958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11576 q selected
  have h3 (q : Pattern) (selected : d133959 q = 1) : d135364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133959, d135364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133959, d135364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133972 q = 1) : d133972 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133973 q = 1) : d135365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133973, d135365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133973, d135365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133974 q = 1) : d135366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133974, d135366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133974, d135366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133975 q = 1) : d135367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133975, d135367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133975, d135367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133976 q = 1) : d135368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133976, d135368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133976, d135368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11578 (p : Pattern) (selected : d133993 p = 1) : d135374 p = 1 := by
  have h0 (q : Pattern) (selected : d133808 q = 1) : d133808 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133894 q = 1) : d135352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133894, d135352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11568 q selected
    | true =>
      simp only [d133894, d135352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11571 q selected
  have h2 (q : Pattern) (selected : d133907 q = 1) : d133907 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d133908 q = 1) : d135353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133908, d135353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133908, d135353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d133909 q = 1) : d135354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133909, d135354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133909, d135354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133910 q = 1) : d135355 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133910, d135355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133910, d135355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133914 q = 1) : d135359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133914, d135359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133914, d135359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11572 q selected
  have h8 (q : Pattern) (selected : d133916 q = 1) : d133916 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d133917 q = 1) : d135360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133917, d135360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133917, d135360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133918 q = 1) : d135361 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133918, d135361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133918, d135361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d133919 q = 1) : d135362 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133919, d135362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133919, d135362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d133920 q = 1) : d135363 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133920, d135363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133920, d135363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d133977 q = 1) : d135369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133977, d135369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133977, d135369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11577 q selected
  have h14 (q : Pattern) (selected : d133988 q = 1) : d133988 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d133989 q = 1) : d135370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133989, d135370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133989, d135370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133990 q = 1) : d135371 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133990, d135371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133990, d135371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d133991 q = 1) : d135372 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133991, d135372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133991, d135372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d133992 q = 1) : d135373 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133992, d135373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133992, d135373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d133993 q = 1) : d135374 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133993, d135374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d133993, d135374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11579 (p : Pattern) (selected : d133999 p = 1) : d135380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d133994 q = 1) : d135375 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133994, d135375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133994, d135375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11578 q selected
  have h2 (q : Pattern) (selected : d133995 q = 1) : d135376 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133995, d135376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133995, d135376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133996 q = 1) : d135377 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133996, d135377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133996, d135377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133997 q = 1) : d135378 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133997, d135378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133997, d135378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133998 q = 1) : d135379 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133998, d135379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133998, d135379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133999 q = 1) : d135380 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133999, d135380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133999, d135380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11580 (p : Pattern) (selected : d134005 p = 1) : d135386 p = 1 := by
  have h0 (q : Pattern) (selected : d133086 q = 1) : d135215 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d133086, d135215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11504 q selected
    | true =>
      simp only [d133086, d135215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11515 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d133313 q = 1) : d135255 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d133313, d135255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133313, d135255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11531 q selected
  have h3 (q : Pattern) (selected : d133314 q = 1) : d135256 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d133314, d135256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133314, d135256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133541 q = 1) : d135296 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d133541, d135296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133541, d135296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11547 q selected
  have h5 (q : Pattern) (selected : d133542 q = 1) : d135297 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d133542, d135297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133542, d135297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133543 q = 1) : d135298 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d133543, d135298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133543, d135298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133770 q = 1) : d135338 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d133770, d135338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133770, d135338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11563 q selected
  have h8 (q : Pattern) (selected : d133771 q = 1) : d135339 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d133771, d135339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133771, d135339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133772 q = 1) : d135340 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d133772, d135340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133772, d135340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133773 q = 1) : d135341 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d133773, d135341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133773, d135341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d134000 q = 1) : d135381 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d134000, d135381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134000, d135381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11579 q selected
  have h12 (q : Pattern) (selected : d134001 q = 1) : d135382 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d134001, d135382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134001, d135382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d134002 q = 1) : d135383 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d134002, d135383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134002, d135383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d134003 q = 1) : d135384 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d134003, d135384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134003, d135384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d134004 q = 1) : d135385 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d134004, d135385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d134004, d135385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d134005 q = 1) : d135386 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d134005, d135386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d134005, d135386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro11581 (p : Pattern) (selected : d134011 p = 1) : d135392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d134006 q = 1) : d135387 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d134006, d135387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11580 q selected
    | true =>
      simp only [d134006, d135387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134007 q = 1) : d135388 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d134007, d135388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134007, d135388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134008 q = 1) : d135389 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d134008, d135389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134008, d135389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134009 q = 1) : d135390 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d134009, d135390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134009, d135390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134010 q = 1) : d135391 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d134010, d135391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134010, d135391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134011 q = 1) : d135392 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d134011, d135392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134011, d135392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11582 (p : Pattern) (selected : d134017 p = 1) : d135398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d134012 q = 1) : d135393 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d134012, d135393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11581 q selected
    | true =>
      simp only [d134012, d135393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134013 q = 1) : d135394 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d134013, d135394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134013, d135394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134014 q = 1) : d135395 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d134014, d135395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134014, d135395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134015 q = 1) : d135396 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d134015, d135396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134015, d135396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134016 q = 1) : d135397 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d134016, d135397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134016, d135397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134017 q = 1) : d135398 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d134017, d135398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134017, d135398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11583 (p : Pattern) (selected : d134023 p = 1) : d135404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d134018 q = 1) : d135399 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d134018, d135399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11582 q selected
    | true =>
      simp only [d134018, d135399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134019 q = 1) : d135400 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d134019, d135400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134019, d135400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134020 q = 1) : d135401 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d134020, d135401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134020, d135401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134021 q = 1) : d135402 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d134021, d135402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134021, d135402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134022 q = 1) : d135403 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d134022, d135403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134022, d135403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134023 q = 1) : d135404 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d134023, d135404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134023, d135404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11584 (p : Pattern) (selected : d134028 p = 1) : d135409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d134024 q = 1) : d135405 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d134024, d135405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11583 q selected
    | true =>
      simp only [d134024, d135405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134025 q = 1) : d135406 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d134025, d135406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134025, d135406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134026 q = 1) : d135407 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d134026, d135407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134026, d135407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134027 q = 1) : d135408 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d134027, d135408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134027, d135408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134028 q = 1) : d135409 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d134028, d135409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134028, d135409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11585 (p : Pattern) (selected : d134034 p = 1) : d135415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d134029 q = 1) : d135410 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d134029, d135410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11584 q selected
    | true =>
      simp only [d134029, d135410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134030 q = 1) : d135411 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d134030, d135411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134030, d135411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134031 q = 1) : d135412 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d134031, d135412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134031, d135412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134032 q = 1) : d135413 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d134032, d135413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134032, d135413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134033 q = 1) : d135414 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d134033, d135414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134033, d135414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134034 q = 1) : d135415 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d134034, d135415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134034, d135415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11586 (p : Pattern) (selected : d134040 p = 1) : d135421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d134035 q = 1) : d135416 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d134035, d135416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11585 q selected
    | true =>
      simp only [d134035, d135416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134036 q = 1) : d135417 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d134036, d135417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134036, d135417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134037 q = 1) : d135418 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d134037, d135418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134037, d135418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134038 q = 1) : d135419 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d134038, d135419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134038, d135419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134039 q = 1) : d135420 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d134039, d135420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134039, d135420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134040 q = 1) : d135421 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d134040, d135421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134040, d135421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11587 (p : Pattern) (selected : d134046 p = 1) : d135427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d134041 q = 1) : d135422 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d134041, d135422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11586 q selected
    | true =>
      simp only [d134041, d135422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134042 q = 1) : d135423 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d134042, d135423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134042, d135423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134043 q = 1) : d135424 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d134043, d135424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134043, d135424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134044 q = 1) : d135425 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d134044, d135425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134044, d135425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134045 q = 1) : d135426 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d134045, d135426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134045, d135426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134046 q = 1) : d135427 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d134046, d135427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134046, d135427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11588 (p : Pattern) (selected : d135437 p = 0) : d136862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135433 q = 0) : d136858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135433, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135433, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6001 q selected
  have h2 (q : Pattern) (selected : d135434 q = 0) : d136859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135434, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135434, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135435 q = 0) : d136860 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135435, d136860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135435, d136860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135436 q = 0) : d136861 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135436, d136861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135436, d136861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135437 q = 0) : d136862 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135437, d136862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135437, d136862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11589 (p : Pattern) (selected : d135443 p = 0) : d136868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135440 q = 0) : d136865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135441 q = 0) : d136866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135441, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135441, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135442 q = 0) : d136867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135442, d136867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135442, d136867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135443 q = 0) : d136868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135443, d136868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135443, d136868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11590 (p : Pattern) (selected : d135449 p = 0) : d136874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135444 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
    | true =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135445 q = 0) : d136870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135445, d136870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135445, d136870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135446 q = 0) : d136871 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135446, d136871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135446, d136871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135447 q = 0) : d136872 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135447, d136872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135447, d136872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135448 q = 0) : d136873 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135448, d136873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135448, d136873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135449 q = 0) : d136874 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135449, d136874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135449, d136874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11591 (p : Pattern) (selected : d135450 p = 0) : d136875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135440 q = 0) : d136865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135441 q = 0) : d136866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135441, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135441, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135442 q = 0) : d136867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135442, d136867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135442, d136867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135450 q = 0) : d136875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135450, d136875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135450, d136875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11592 (p : Pattern) (selected : d135456 p = 0) : d136881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135444 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
    | true =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135445 q = 0) : d136870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135445, d136870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135445, d136870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135446 q = 0) : d136871 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135446, d136871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135446, d136871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135447 q = 0) : d136872 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135447, d136872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135447, d136872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135448 q = 0) : d136873 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135448, d136873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135448, d136873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135451 q = 0) : d136876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
    | true =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135452 q = 0) : d136877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135452, d136877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135452, d136877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135453 q = 0) : d136878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135453, d136878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135453, d136878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135454 q = 0) : d136879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135454, d136879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135454, d136879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135455 q = 0) : d136880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135455, d136880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135455, d136880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135456 q = 0) : d136881 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135456, d136881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135456, d136881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11593 (p : Pattern) (selected : d135461 p = 0) : d136886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135451 q = 0) : d136876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
    | true =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135452 q = 0) : d136877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135452, d136877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135452, d136877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135453 q = 0) : d136878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135453, d136878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135453, d136878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135454 q = 0) : d136879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135454, d136879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135454, d136879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135455 q = 0) : d136880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135455, d136880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135455, d136880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135461 q = 0) : d136886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135461, d136886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135461, d136886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11594 (p : Pattern) (selected : d135471 p = 0) : d136896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135467 q = 0) : d136892 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135467, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135467, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6008 q selected
  have h2 (q : Pattern) (selected : d135468 q = 0) : d136893 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135468, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135468, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135469 q = 0) : d136894 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135469, d136894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135469, d136894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135470 q = 0) : d136895 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135470, d136895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135470, d136895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135471 q = 0) : d136896 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135471, d136896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135471, d136896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11595 (p : Pattern) (selected : d135477 p = 0) : d136902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135472 q = 0) : d136897 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135472, d136897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11594 q selected
    | true =>
      simp only [d135472, d136897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135473 q = 0) : d136898 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135473, d136898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135473, d136898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135474 q = 0) : d136899 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135474, d136899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135474, d136899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135475 q = 0) : d136900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135475, d136900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135475, d136900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135476 q = 0) : d136901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135476, d136901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135476, d136901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135477 q = 0) : d136902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135477, d136902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135477, d136902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11596 (p : Pattern) (selected : d135483 p = 0) : d136908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135478 q = 0) : d136903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135478, d136903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11595 q selected
    | true =>
      simp only [d135478, d136903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135479 q = 0) : d136904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135479, d136904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135479, d136904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135480 q = 0) : d136905 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135480, d136905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135480, d136905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135481 q = 0) : d136906 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135481, d136906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135481, d136906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135482 q = 0) : d136907 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135482, d136907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135482, d136907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135483 q = 0) : d136908 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135483, d136908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135483, d136908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11597 (p : Pattern) (selected : d135489 p = 0) : d136914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135457 q = 0) : d136882 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135457, d136882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11590 q selected
    | true =>
      simp only [d135457, d136882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11592 q selected
  have h2 (q : Pattern) (selected : d135458 q = 0) : d136883 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135458, d136883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135458, d136883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135459 q = 0) : d136884 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135459, d136884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135459, d136884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135460 q = 0) : d136885 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135460, d136885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135460, d136885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135462 q = 0) : d136887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135462, d136887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135462, d136887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11593 q selected
  have h6 (q : Pattern) (selected : d135463 q = 0) : d136888 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135463, d136888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135463, d136888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135464 q = 0) : d136889 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135464, d136889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135464, d136889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135465 q = 0) : d136890 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135465, d136890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135465, d136890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135466 q = 0) : d136891 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135466, d136891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135466, d136891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135484 q = 0) : d136909 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135484, d136909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135484, d136909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11596 q selected
  have h11 (q : Pattern) (selected : d135485 q = 0) : d136910 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135485, d136910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135485, d136910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135486 q = 0) : d136911 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135486, d136911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135486, d136911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d135487 q = 0) : d136912 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135487, d136912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d135487, d136912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d135488 q = 0) : d136913 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135488, d136913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d135488, d136913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d135489 q = 0) : d136914 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d135489, d136914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135489, d136914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro11598 (p : Pattern) (selected : d135499 p = 0) : d136924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135444 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
    | true =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135495 q = 0) : d136920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135495, d136920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135495, d136920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135496 q = 0) : d136921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135496, d136921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135496, d136921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135497 q = 0) : d136922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135497, d136922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135497, d136922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135498 q = 0) : d136923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135498, d136923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135498, d136923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135499 q = 0) : d136924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135499, d136924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135499, d136924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11599 (p : Pattern) (selected : d135506 p = 0) : d136931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135444 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
    | true =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135495 q = 0) : d136920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135495, d136920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135495, d136920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135496 q = 0) : d136921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135496, d136921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135496, d136921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135497 q = 0) : d136922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135497, d136922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135497, d136922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135498 q = 0) : d136923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135498, d136923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135498, d136923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135451 q = 0) : d136876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
    | true =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135502 q = 0) : d136927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135502, d136927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135502, d136927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135503 q = 0) : d136928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135503, d136928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135503, d136928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135504 q = 0) : d136929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135504, d136929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135504, d136929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135505 q = 0) : d136930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135505, d136930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135505, d136930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135506 q = 0) : d136931 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135506, d136931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135506, d136931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11600 (p : Pattern) (selected : d135511 p = 0) : d136936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135440 q = 0) : d136865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135441 q = 0) : d136866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135441, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135441, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135510 q = 0) : d136935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135510, d136935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135510, d136935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135511 q = 0) : d136936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135511, d136936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135511, d136936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11601 (p : Pattern) (selected : d135518 p = 0) : d136943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135440 q = 0) : d136865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135516 q = 0) : d136941 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135516, d136941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135516, d136941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135517 q = 0) : d136942 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135517, d136942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135517, d136942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135518 q = 0) : d136943 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135518, d136943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135518, d136943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11602 (p : Pattern) (selected : d135526 p = 0) : d136951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135522 q = 0) : d136947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135522, d136947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135522, d136947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6017 q selected
  have h2 (q : Pattern) (selected : d135523 q = 0) : d136948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135523, d136948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135523, d136948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135433 q = 0) : d136858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135433, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135433, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6001 q selected
  have h4 (q : Pattern) (selected : d135434 q = 0) : d136859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135434, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135434, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135524 q = 0) : d136949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135524, d136949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135524, d136949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135435 q = 0) : d136860 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135435, d136860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135435, d136860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135525 q = 0) : d136950 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135525, d136950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135525, d136950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135526 q = 0) : d136951 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135526, d136951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135526, d136951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11603 (p : Pattern) (selected : d135532 p = 0) : d136957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135529 q = 0) : d136954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135530 q = 0) : d136955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135530, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135530, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135531 q = 0) : d136956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135531, d136956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135531, d136956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135532 q = 0) : d136957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135532, d136957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135532, d136957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11604 (p : Pattern) (selected : d135538 p = 0) : d136862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135534 q = 0) : d136858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135534, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135534, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6020 q selected
  have h2 (q : Pattern) (selected : d135535 q = 0) : d136859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135535, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135535, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135536 q = 0) : d136860 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135536, d136860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135536, d136860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135537 q = 0) : d136861 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135537, d136861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135537, d136861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135538 q = 0) : d136862 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135538, d136862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135538, d136862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11605 (p : Pattern) (selected : d135544 p = 0) : d136868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135539 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135539, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11604 q selected
    | true =>
      simp only [d135539, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135540 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135540, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135540, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135541 q = 0) : d136865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135541, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135541, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135542 q = 0) : d136866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135542, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135542, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135543 q = 0) : d136867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135543, d136867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135543, d136867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135544 q = 0) : d136868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135544, d136868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135544, d136868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11606 (p : Pattern) (selected : d135550 p = 0) : d136963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135512 q = 0) : d136937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135512, d136937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11600 q selected
    | true =>
      simp only [d135512, d136937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135513 q = 0) : d136938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135513, d136938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135513, d136938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135514 q = 0) : d136939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135514, d136939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135514, d136939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135515 q = 0) : d136940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135515, d136940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135515, d136940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135519 q = 0) : d136944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135519, d136944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11601 q selected
    | true =>
      simp only [d135519, d136944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135520 q = 0) : d136945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135520, d136945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135520, d136945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135521 q = 0) : d136946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135521, d136946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135521, d136946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135533 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
    | true =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
  have h9 (q : Pattern) (selected : d135545 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135545, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11605 q selected
    | true =>
      simp only [d135545, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d135546 q = 0) : d136959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135546, d136959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135546, d136959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135444 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
    | true =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135445 q = 0) : d136870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135445, d136870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135445, d136870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d135547 q = 0) : d136960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135547, d136960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135547, d136960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135548 q = 0) : d136961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135548, d136961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135548, d136961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d135549 q = 0) : d136962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135549, d136962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135549, d136962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135550 q = 0) : d136963 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135550, d136963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135550, d136963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11607 (p : Pattern) (selected : d135551 p = 0) : d136964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135440 q = 0) : d136865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135441 q = 0) : d136866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135441, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135441, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135510 q = 0) : d136935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135510, d136935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135510, d136935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135551 q = 0) : d136964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135551, d136964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135551, d136964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11608 (p : Pattern) (selected : d135556 p = 0) : d136969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135440 q = 0) : d136865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135440, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135516 q = 0) : d136941 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135516, d136941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135516, d136941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135517 q = 0) : d136942 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135517, d136942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135517, d136942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135556 q = 0) : d136969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135556, d136969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135556, d136969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11609 (p : Pattern) (selected : d135560 p = 0) : d136973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135529 q = 0) : d136954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135530 q = 0) : d136955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135530, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135530, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135531 q = 0) : d136956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135531, d136956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135531, d136956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135560 q = 0) : d136973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135560, d136973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135560, d136973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11610 (p : Pattern) (selected : d135562 p = 0) : d136875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135539 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135539, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11604 q selected
    | true =>
      simp only [d135539, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135540 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135540, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135540, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135541 q = 0) : d136865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135541, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135541, d136865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135542 q = 0) : d136866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135542, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135542, d136866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135543 q = 0) : d136867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135543, d136867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135543, d136867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135562 q = 0) : d136875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135562, d136875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135562, d136875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11611 (p : Pattern) (selected : d135568 p = 0) : d136979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135512 q = 0) : d136937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135512, d136937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11600 q selected
    | true =>
      simp only [d135512, d136937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135513 q = 0) : d136938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135513, d136938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135513, d136938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135514 q = 0) : d136939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135514, d136939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135514, d136939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135515 q = 0) : d136940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135515, d136940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135515, d136940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135519 q = 0) : d136944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135519, d136944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11601 q selected
    | true =>
      simp only [d135519, d136944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135520 q = 0) : d136945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135520, d136945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135520, d136945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135521 q = 0) : d136946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135521, d136946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135521, d136946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135533 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
    | true =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
  have h9 (q : Pattern) (selected : d135545 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135545, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11605 q selected
    | true =>
      simp only [d135545, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d135546 q = 0) : d136959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135546, d136959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135546, d136959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135444 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
    | true =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135445 q = 0) : d136870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135445, d136870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135445, d136870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d135547 q = 0) : d136960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135547, d136960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135547, d136960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135548 q = 0) : d136961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135548, d136961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135548, d136961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d135549 q = 0) : d136962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135549, d136962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135549, d136962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135552 q = 0) : d136965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135552, d136965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11607 q selected
    | true =>
      simp only [d135552, d136965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d135553 q = 0) : d136966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135553, d136966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135553, d136966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d135554 q = 0) : d136967 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135554, d136967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d135554, d136967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d135555 q = 0) : d136968 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135555, d136968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135555, d136968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d135557 q = 0) : d136970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135557, d136970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11608 q selected
    | true =>
      simp only [d135557, d136970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d135558 q = 0) : d136971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135558, d136971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135558, d136971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d135559 q = 0) : d136972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135559, d136972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d135559, d136972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d135561 q = 0) : d136974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135561, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11609 q selected
    | true =>
      simp only [d135561, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
  have h24 (q : Pattern) (selected : d135563 q = 0) : d136876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135563, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11610 q selected
    | true =>
      simp only [d135563, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d135564 q = 0) : d136975 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135564, d136975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d135564, d136975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d135451 q = 0) : d136876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
    | true =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d135452 q = 0) : d136877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135452, d136877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d135452, d136877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d135565 q = 0) : d136976 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135565, d136976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d135565, d136976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d135566 q = 0) : d136977 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135566, d136977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d135566, d136977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d135567 q = 0) : d136978 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135567, d136978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d135567, d136978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d135568 q = 0) : d136979 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135568, d136979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d135568, d136979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11612 (p : Pattern) (selected : d135570 p = 0) : d136981 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135444 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
    | true =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135495 q = 0) : d136920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135495, d136920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135495, d136920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135496 q = 0) : d136921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135496, d136921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135496, d136921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135497 q = 0) : d136922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135497, d136922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135497, d136922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135498 q = 0) : d136923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135498, d136923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135498, d136923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135570 q = 0) : d136981 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135570, d136981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135570, d136981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11613 (p : Pattern) (selected : d135577 p = 0) : d136988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135561 q = 0) : d136974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135561, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11609 q selected
    | true =>
      simp only [d135561, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
  have h2 (q : Pattern) (selected : d135563 q = 0) : d136876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135563, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11610 q selected
    | true =>
      simp only [d135563, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135564 q = 0) : d136975 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135564, d136975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135564, d136975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135451 q = 0) : d136876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
    | true =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135452 q = 0) : d136877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135452, d136877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135452, d136877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135565 q = 0) : d136976 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135565, d136976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135565, d136976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135575 q = 0) : d136986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135575, d136986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135575, d136986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135576 q = 0) : d136987 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135576, d136987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135576, d136987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135577 q = 0) : d136988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135577, d136988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135577, d136988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11614 (p : Pattern) (selected : d135587 p = 0) : d136998 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135583 q = 0) : d136994 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135583, d136994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135583, d136994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6031 q selected
  have h2 (q : Pattern) (selected : d135584 q = 0) : d136995 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135584, d136995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135584, d136995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135467 q = 0) : d136892 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135467, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135467, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6008 q selected
  have h4 (q : Pattern) (selected : d135468 q = 0) : d136893 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135468, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135468, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135585 q = 0) : d136996 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135585, d136996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135585, d136996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135469 q = 0) : d136894 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135469, d136894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135469, d136894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135586 q = 0) : d136997 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135586, d136997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135586, d136997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135587 q = 0) : d136998 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135587, d136998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135587, d136998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11615 (p : Pattern) (selected : d135593 p = 0) : d137004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135588 q = 0) : d136999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135588, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11614 q selected
    | true =>
      simp only [d135588, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135589 q = 0) : d137000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135589, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135589, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135472 q = 0) : d136897 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135472, d136897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11594 q selected
    | true =>
      simp only [d135472, d136897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135473 q = 0) : d136898 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135473, d136898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135473, d136898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135590 q = 0) : d137001 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135590, d137001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135590, d137001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135591 q = 0) : d137002 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135591, d137002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135591, d137002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135592 q = 0) : d137003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135592, d137003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135592, d137003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135593 q = 0) : d137004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135593, d137004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135593, d137004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11616 (p : Pattern) (selected : d135599 p = 0) : d136896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135595 q = 0) : d136892 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135595, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135595, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6034 q selected
  have h2 (q : Pattern) (selected : d135596 q = 0) : d136893 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135596, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135596, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135597 q = 0) : d136894 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135597, d136894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135597, d136894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135598 q = 0) : d136895 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135598, d136895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135598, d136895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135599 q = 0) : d136896 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135599, d136896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135599, d136896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11617 (p : Pattern) (selected : d135605 p = 0) : d136902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135600 q = 0) : d136897 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135600, d136897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11616 q selected
    | true =>
      simp only [d135600, d136897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135601 q = 0) : d136898 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135601, d136898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135601, d136898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135602 q = 0) : d136899 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135602, d136899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135602, d136899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135603 q = 0) : d136900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135603, d136900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135603, d136900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135604 q = 0) : d136901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135604, d136901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135604, d136901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135605 q = 0) : d136902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135605, d136902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135605, d136902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11618 (p : Pattern) (selected : d135611 p = 0) : d137010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135594 q = 0) : d137005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135594, d137005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11615 q selected
    | true =>
      simp only [d135594, d137005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11595 q selected
  have h2 (q : Pattern) (selected : d135606 q = 0) : d136903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135606, d136903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11617 q selected
    | true =>
      simp only [d135606, d136903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135607 q = 0) : d137006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135607, d137006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135607, d137006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135478 q = 0) : d136903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135478, d136903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11595 q selected
    | true =>
      simp only [d135478, d136903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135479 q = 0) : d136904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135479, d136904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135479, d136904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135608 q = 0) : d137007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135608, d137007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135608, d137007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135609 q = 0) : d137008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135609, d137008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135609, d137008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135610 q = 0) : d137009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135610, d137009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135610, d137009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135611 q = 0) : d137010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135611, d137010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135611, d137010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11619 (p : Pattern) (selected : d135617 p = 0) : d137016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135500 q = 0) : d136925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135500, d136925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135500, d136925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11598 q selected
  have h2 (q : Pattern) (selected : d135501 q = 0) : d136926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135501, d136926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135501, d136926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135507 q = 0) : d136932 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135507, d136932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11598 q selected
    | true =>
      simp only [d135507, d136932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11599 q selected
  have h4 (q : Pattern) (selected : d135508 q = 0) : d136933 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135508, d136933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135508, d136933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135509 q = 0) : d136934 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135509, d136934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135509, d136934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135569 q = 0) : d136980 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135569, d136980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11606 q selected
    | true =>
      simp only [d135569, d136980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11611 q selected
  have h7 (q : Pattern) (selected : d135571 q = 0) : d136982 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135571, d136982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11612 q selected
    | true =>
      simp only [d135571, d136982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135572 q = 0) : d136983 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135572, d136983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135572, d136983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135573 q = 0) : d136984 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135573, d136984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135573, d136984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d135574 q = 0) : d136985 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135574, d136985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135574, d136985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135578 q = 0) : d136989 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135578, d136989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135578, d136989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11613 q selected
  have h12 (q : Pattern) (selected : d135579 q = 0) : d136990 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135579, d136990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135579, d136990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d135580 q = 0) : d136991 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135580, d136991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d135580, d136991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d135581 q = 0) : d136992 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135581, d136992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d135581, d136992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d135582 q = 0) : d136993 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135582, d136993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135582, d136993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135612 q = 0) : d137011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135612, d137011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135612, d137011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11618 q selected
  have h17 (q : Pattern) (selected : d135613 q = 0) : d137012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135613, d137012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d135613, d137012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d135614 q = 0) : d137013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135614, d137013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d135614, d137013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d135615 q = 0) : d137014 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135615, d137014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d135615, d137014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d135616 q = 0) : d137015 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135616, d137015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d135616, d137015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d135617 q = 0) : d137016 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d135617, d137016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d135617, d137016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro11620 (p : Pattern) (selected : d135623 p = 0) : d137022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135490 q = 0) : d136915 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d135490, d136915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135490, d136915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11597 q selected
  have h2 (q : Pattern) (selected : d135491 q = 0) : d136916 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d135491, d136916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135491, d136916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135492 q = 0) : d136917 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d135492, d136917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135492, d136917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135493 q = 0) : d136918 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d135493, d136918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135493, d136918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135494 q = 0) : d136919 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d135494, d136919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135494, d136919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135618 q = 0) : d137017 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d135618, d137017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135618, d137017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11619 q selected
  have h7 (q : Pattern) (selected : d135619 q = 0) : d137018 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d135619, d137018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135619, d137018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135620 q = 0) : d137019 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d135620, d137019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135620, d137019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135621 q = 0) : d137020 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d135621, d137020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135621, d137020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135622 q = 0) : d137021 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d135622, d137021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135622, d137021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135623 q = 0) : d137022 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d135623, d137022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135623, d137022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11621 (p : Pattern) (selected : d135628 p = 0) : d137027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135533 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
    | true =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
  have h2 (q : Pattern) (selected : d135624 q = 0) : d137023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135624, d137023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135624, d137023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135625 q = 0) : d137024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135625, d137024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135625, d137024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135626 q = 0) : d137025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135626, d137025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135626, d137025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135627 q = 0) : d137026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135627, d137026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135627, d137026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135628 q = 0) : d137027 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135628, d137027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135628, d137027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11622 (p : Pattern) (selected : d135635 p = 0) : d137034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135533 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
    | true =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
  have h2 (q : Pattern) (selected : d135624 q = 0) : d137023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135624, d137023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135624, d137023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135625 q = 0) : d137024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135625, d137024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135625, d137024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135626 q = 0) : d137025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135626, d137025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135626, d137025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135627 q = 0) : d137026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135627, d137026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135627, d137026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135561 q = 0) : d136974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135561, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11609 q selected
    | true =>
      simp only [d135561, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
  have h7 (q : Pattern) (selected : d135631 q = 0) : d137030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135631, d137030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135631, d137030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135632 q = 0) : d137031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135632, d137031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135632, d137031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135633 q = 0) : d137032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135633, d137032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135633, d137032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135634 q = 0) : d137033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135634, d137033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135634, d137033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135635 q = 0) : d137034 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135635, d137034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135635, d137034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11623 (p : Pattern) (selected : d135640 p = 0) : d137039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135529 q = 0) : d136954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135530 q = 0) : d136955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135530, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135530, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135639 q = 0) : d137038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135639, d137038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135639, d137038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135640 q = 0) : d137039 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135640, d137039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135640, d137039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11624 (p : Pattern) (selected : d135647 p = 0) : d137046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135529 q = 0) : d136954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135645 q = 0) : d137044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135645, d137044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135645, d137044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135646 q = 0) : d137045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135646, d137045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135646, d137045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135647 q = 0) : d137046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135647, d137046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135647, d137046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11625 (p : Pattern) (selected : d135655 p = 0) : d137054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135651 q = 0) : d137050 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135651, d137050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135651, d137050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6044 q selected
  have h2 (q : Pattern) (selected : d135652 q = 0) : d137051 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135652, d137051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135652, d137051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135522 q = 0) : d136947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135522, d136947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135522, d136947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6017 q selected
  have h4 (q : Pattern) (selected : d135523 q = 0) : d136948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135523, d136948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135523, d136948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135653 q = 0) : d137052 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135653, d137052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135653, d137052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135433 q = 0) : d136858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135433, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135433, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6001 q selected
  have h7 (q : Pattern) (selected : d135434 q = 0) : d136859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135434, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135434, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135524 q = 0) : d136949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135524, d136949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135524, d136949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135654 q = 0) : d137053 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135654, d137053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135654, d137053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135655 q = 0) : d137054 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135655, d137054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135655, d137054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11626 (p : Pattern) (selected : d135661 p = 0) : d137060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135656 q = 0) : d137055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135656, d137055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11625 q selected
    | true =>
      simp only [d135656, d137055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135657 q = 0) : d137056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135657, d137056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135657, d137056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135658 q = 0) : d137057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135658, d137057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135658, d137057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135659 q = 0) : d137058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135659, d137058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135659, d137058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135660 q = 0) : d137059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135660, d137059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135660, d137059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135661 q = 0) : d137060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135661, d137060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135661, d137060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11627 (p : Pattern) (selected : d135667 p = 0) : d136951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135663 q = 0) : d136947 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135663, d136947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135663, d136947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6049 q selected
  have h2 (q : Pattern) (selected : d135664 q = 0) : d136948 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135664, d136948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135664, d136948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135534 q = 0) : d136858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135534, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135534, d136858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6020 q selected
  have h4 (q : Pattern) (selected : d135535 q = 0) : d136859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135535, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135535, d136859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135665 q = 0) : d136949 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135665, d136949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135665, d136949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135536 q = 0) : d136860 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135536, d136860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135536, d136860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135666 q = 0) : d136950 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135666, d136950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135666, d136950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135667 q = 0) : d136951 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135667, d136951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135667, d136951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11628 (p : Pattern) (selected : d135673 p = 0) : d136957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135668 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135668, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11627 q selected
    | true =>
      simp only [d135668, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135669 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135669, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135669, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135539 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135539, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11604 q selected
    | true =>
      simp only [d135539, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135540 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135540, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135540, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135670 q = 0) : d136954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135670, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135670, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135671 q = 0) : d136955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135671, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135671, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135672 q = 0) : d136956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135672, d136956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135672, d136956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135673 q = 0) : d136957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135673, d136957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135673, d136957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11629 (p : Pattern) (selected : d135679 p = 0) : d137066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135676 q = 0) : d137063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135676, d137063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135676, d137063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135677 q = 0) : d137064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135677, d137064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135677, d137064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135678 q = 0) : d137065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135678, d137065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135678, d137065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135679 q = 0) : d137066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135679, d137066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135679, d137066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11630 (p : Pattern) (selected : d135685 p = 0) : d137072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135641 q = 0) : d137040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135641, d137040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11623 q selected
    | true =>
      simp only [d135641, d137040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11600 q selected
  have h2 (q : Pattern) (selected : d135642 q = 0) : d137041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135642, d137041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135642, d137041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135643 q = 0) : d137042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135643, d137042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135643, d137042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135644 q = 0) : d137043 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135644, d137043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135644, d137043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135648 q = 0) : d137047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135648, d137047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11624 q selected
    | true =>
      simp only [d135648, d137047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11601 q selected
  have h6 (q : Pattern) (selected : d135649 q = 0) : d137048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135649, d137048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135649, d137048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135650 q = 0) : d137049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135650, d137049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135650, d137049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135662 q = 0) : d137061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135662, d137061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11626 q selected
    | true =>
      simp only [d135662, d137061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
  have h9 (q : Pattern) (selected : d135674 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135674, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11628 q selected
    | true =>
      simp only [d135674, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11605 q selected
  have h10 (q : Pattern) (selected : d135675 q = 0) : d137062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135675, d137062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135675, d137062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135680 q = 0) : d137067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135680, d137067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11629 q selected
    | true =>
      simp only [d135680, d137067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135681 q = 0) : d137068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135681, d137068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135681, d137068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d135682 q = 0) : d137069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135682, d137069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135682, d137069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135683 q = 0) : d137070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135683, d137070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135683, d137070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d135684 q = 0) : d137071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135684, d137071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135684, d137071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135685 q = 0) : d137072 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135685, d137072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135685, d137072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11631 (p : Pattern) (selected : d135686 p = 0) : d137073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135529 q = 0) : d136954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135530 q = 0) : d136955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135530, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135530, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135639 q = 0) : d137038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135639, d137038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135639, d137038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135686 q = 0) : d137073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135686, d137073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135686, d137073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11632 (p : Pattern) (selected : d135691 p = 0) : d137078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135438 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11588 q selected
    | true =>
      simp only [d135438, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135439 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135439, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135529 q = 0) : d136954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135529, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135645 q = 0) : d137044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135645, d137044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135645, d137044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135646 q = 0) : d137045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135646, d137045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135646, d137045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135691 q = 0) : d137078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135691, d137078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135691, d137078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11633 (p : Pattern) (selected : d135695 p = 0) : d137082 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135656 q = 0) : d137055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135656, d137055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11625 q selected
    | true =>
      simp only [d135656, d137055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135657 q = 0) : d137056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135657, d137056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135657, d137056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135658 q = 0) : d137057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135658, d137057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135658, d137057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135659 q = 0) : d137058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135659, d137058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135659, d137058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135660 q = 0) : d137059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135660, d137059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135660, d137059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135695 q = 0) : d137082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135695, d137082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135695, d137082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11634 (p : Pattern) (selected : d135697 p = 0) : d136973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135668 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135668, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11627 q selected
    | true =>
      simp only [d135668, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135669 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135669, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135669, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135539 q = 0) : d136863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135539, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11604 q selected
    | true =>
      simp only [d135539, d136863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135540 q = 0) : d136864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135540, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135540, d136864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135670 q = 0) : d136954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135670, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135670, d136954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135671 q = 0) : d136955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135671, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135671, d136955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135672 q = 0) : d136956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135672, d136956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135672, d136956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135697 q = 0) : d136973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135697, d136973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135697, d136973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11635 (p : Pattern) (selected : d135700 p = 0) : d137085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135527 q = 0) : d136952 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11602 q selected
    | true =>
      simp only [d135527, d136952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135528 q = 0) : d136953 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135528, d136953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135676 q = 0) : d137063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135676, d137063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135676, d137063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135677 q = 0) : d137064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135677, d137064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135677, d137064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135678 q = 0) : d137065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135678, d137065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135678, d137065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135700 q = 0) : d137085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135700, d137085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135700, d137085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11636 (p : Pattern) (selected : d135706 p = 0) : d137091 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135641 q = 0) : d137040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135641, d137040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11623 q selected
    | true =>
      simp only [d135641, d137040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11600 q selected
  have h2 (q : Pattern) (selected : d135642 q = 0) : d137041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135642, d137041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135642, d137041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135643 q = 0) : d137042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135643, d137042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135643, d137042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135644 q = 0) : d137043 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135644, d137043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135644, d137043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135648 q = 0) : d137047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135648, d137047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11624 q selected
    | true =>
      simp only [d135648, d137047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11601 q selected
  have h6 (q : Pattern) (selected : d135649 q = 0) : d137048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135649, d137048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135649, d137048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135650 q = 0) : d137049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135650, d137049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135650, d137049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135662 q = 0) : d137061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135662, d137061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11626 q selected
    | true =>
      simp only [d135662, d137061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
  have h9 (q : Pattern) (selected : d135674 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135674, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11628 q selected
    | true =>
      simp only [d135674, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11605 q selected
  have h10 (q : Pattern) (selected : d135675 q = 0) : d137062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135675, d137062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135675, d137062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135680 q = 0) : d137067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135680, d137067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11629 q selected
    | true =>
      simp only [d135680, d137067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135681 q = 0) : d137068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135681, d137068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135681, d137068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d135682 q = 0) : d137069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135682, d137069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135682, d137069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135683 q = 0) : d137070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135683, d137070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135683, d137070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d135684 q = 0) : d137071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135684, d137071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135684, d137071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135687 q = 0) : d137074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135687, d137074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11631 q selected
    | true =>
      simp only [d135687, d137074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11607 q selected
  have h17 (q : Pattern) (selected : d135688 q = 0) : d137075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135688, d137075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135688, d137075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d135689 q = 0) : d137076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135689, d137076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d135689, d137076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d135690 q = 0) : d137077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135690, d137077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135690, d137077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d135692 q = 0) : d137079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135692, d137079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11632 q selected
    | true =>
      simp only [d135692, d137079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11608 q selected
  have h21 (q : Pattern) (selected : d135693 q = 0) : d137080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135693, d137080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135693, d137080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d135694 q = 0) : d137081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135694, d137081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d135694, d137081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d135696 q = 0) : d137083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135696, d137083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11633 q selected
    | true =>
      simp only [d135696, d137083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11609 q selected
  have h24 (q : Pattern) (selected : d135698 q = 0) : d136974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135698, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11634 q selected
    | true =>
      simp only [d135698, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11610 q selected
  have h25 (q : Pattern) (selected : d135699 q = 0) : d137084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135699, d137084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d135699, d137084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d135701 q = 0) : d137086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135701, d137086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11635 q selected
    | true =>
      simp only [d135701, d137086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d135702 q = 0) : d137087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135702, d137087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d135702, d137087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d135703 q = 0) : d137088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135703, d137088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d135703, d137088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d135704 q = 0) : d137089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135704, d137089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d135704, d137089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d135705 q = 0) : d137090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135705, d137090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d135705, d137090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d135706 q = 0) : d137091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135706, d137091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d135706, d137091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11637 (p : Pattern) (selected : d135708 p = 0) : d137093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135533 q = 0) : d136958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11603 q selected
    | true =>
      simp only [d135533, d136958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
  have h2 (q : Pattern) (selected : d135624 q = 0) : d137023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135624, d137023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135624, d137023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135625 q = 0) : d137024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135625, d137024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135625, d137024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135626 q = 0) : d137025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135626, d137025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135626, d137025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135627 q = 0) : d137026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135627, d137026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135627, d137026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135444 q = 0) : d136869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11589 q selected
    | true =>
      simp only [d135444, d136869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135495 q = 0) : d136920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135495, d136920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135495, d136920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135496 q = 0) : d136921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135496, d136921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135496, d136921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135497 q = 0) : d136922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135497, d136922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135497, d136922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135498 q = 0) : d136923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135498, d136923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135498, d136923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135708 q = 0) : d137093 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135708, d137093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135708, d137093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11638 (p : Pattern) (selected : d135715 p = 0) : d137100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135696 q = 0) : d137083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135696, d137083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11633 q selected
    | true =>
      simp only [d135696, d137083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11609 q selected
  have h2 (q : Pattern) (selected : d135698 q = 0) : d136974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135698, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11634 q selected
    | true =>
      simp only [d135698, d136974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11610 q selected
  have h3 (q : Pattern) (selected : d135699 q = 0) : d137084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135699, d137084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135699, d137084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135701 q = 0) : d137086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135701, d137086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11635 q selected
    | true =>
      simp only [d135701, d137086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135702 q = 0) : d137087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135702, d137087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135702, d137087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135703 q = 0) : d137088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135703, d137088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135703, d137088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135713 q = 0) : d137098 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135713, d137098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135713, d137098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135714 q = 0) : d137099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135714, d137099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135714, d137099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135715 q = 0) : d137100 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135715, d137100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135715, d137100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11639 (p : Pattern) (selected : d135717 p = 0) : d137102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135451 q = 0) : d136876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11591 q selected
    | true =>
      simp only [d135451, d136876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135502 q = 0) : d136927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135502, d136927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135502, d136927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135503 q = 0) : d136928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135503, d136928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135503, d136928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135504 q = 0) : d136929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135504, d136929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135504, d136929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135505 q = 0) : d136930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135505, d136930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135505, d136930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135717 q = 0) : d137102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135717, d137102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135717, d137102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11640 (p : Pattern) (selected : d135727 p = 0) : d137112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135723 q = 0) : d137108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135723, d137108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135723, d137108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6064 q selected
  have h2 (q : Pattern) (selected : d135724 q = 0) : d137109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135724, d137109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135724, d137109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135583 q = 0) : d136994 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135583, d136994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135583, d136994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6031 q selected
  have h4 (q : Pattern) (selected : d135584 q = 0) : d136995 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135584, d136995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135584, d136995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135725 q = 0) : d137110 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135725, d137110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135725, d137110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135467 q = 0) : d136892 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135467, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135467, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6008 q selected
  have h7 (q : Pattern) (selected : d135468 q = 0) : d136893 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135468, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135468, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135585 q = 0) : d136996 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135585, d136996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135585, d136996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135726 q = 0) : d137111 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135726, d137111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135726, d137111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135727 q = 0) : d137112 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135727, d137112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135727, d137112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11641 (p : Pattern) (selected : d135733 p = 0) : d137118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135728 q = 0) : d137113 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135728, d137113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11640 q selected
    | true =>
      simp only [d135728, d137113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135729 q = 0) : d137114 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135729, d137114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135729, d137114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135588 q = 0) : d136999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135588, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11614 q selected
    | true =>
      simp only [d135588, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135589 q = 0) : d137000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135589, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135589, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135730 q = 0) : d137115 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135730, d137115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135730, d137115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135731 q = 0) : d137116 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135731, d137116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135731, d137116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135732 q = 0) : d137117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135732, d137117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135732, d137117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135733 q = 0) : d137118 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135733, d137118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135733, d137118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11642 (p : Pattern) (selected : d135739 p = 0) : d136998 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135735 q = 0) : d136994 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135735, d136994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135735, d136994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6069 q selected
  have h2 (q : Pattern) (selected : d135736 q = 0) : d136995 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135736, d136995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135736, d136995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135595 q = 0) : d136892 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135595, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135595, d136892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6034 q selected
  have h4 (q : Pattern) (selected : d135596 q = 0) : d136893 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135596, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135596, d136893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135737 q = 0) : d136996 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135737, d136996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135737, d136996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135597 q = 0) : d136894 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135597, d136894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135597, d136894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135738 q = 0) : d136997 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135738, d136997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135738, d136997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135739 q = 0) : d136998 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135739, d136998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135739, d136998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11643 (p : Pattern) (selected : d135745 p = 0) : d137004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135740 q = 0) : d136999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135740, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11642 q selected
    | true =>
      simp only [d135740, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135741 q = 0) : d137000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135741, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135741, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135600 q = 0) : d136897 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135600, d136897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11616 q selected
    | true =>
      simp only [d135600, d136897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135601 q = 0) : d136898 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135601, d136898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135601, d136898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135742 q = 0) : d137001 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135742, d137001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135742, d137001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135743 q = 0) : d137002 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135743, d137002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135743, d137002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135744 q = 0) : d137003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135744, d137003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135744, d137003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135745 q = 0) : d137004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135745, d137004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135745, d137004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11644 (p : Pattern) (selected : d135751 p = 0) : d137124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135588 q = 0) : d136999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135588, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11614 q selected
    | true =>
      simp only [d135588, d136999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135589 q = 0) : d137000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135589, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135589, d137000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135748 q = 0) : d137121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135748, d137121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135748, d137121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135749 q = 0) : d137122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135749, d137122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135749, d137122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135750 q = 0) : d137123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135750, d137123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135750, d137123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135751 q = 0) : d137124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135751, d137124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135751, d137124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11645 (p : Pattern) (selected : d135757 p = 0) : d137130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135734 q = 0) : d137119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135734, d137119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11641 q selected
    | true =>
      simp only [d135734, d137119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11615 q selected
  have h2 (q : Pattern) (selected : d135746 q = 0) : d137005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135746, d137005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11643 q selected
    | true =>
      simp only [d135746, d137005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11617 q selected
  have h3 (q : Pattern) (selected : d135747 q = 0) : d137120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135747, d137120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135747, d137120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135752 q = 0) : d137125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135752, d137125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11644 q selected
    | true =>
      simp only [d135752, d137125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135753 q = 0) : d137126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135753, d137126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135753, d137126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135754 q = 0) : d137127 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135754, d137127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135754, d137127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135755 q = 0) : d137128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135755, d137128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135755, d137128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135756 q = 0) : d137129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135756, d137129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135756, d137129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135757 q = 0) : d137130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135757, d137130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135757, d137130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11646 (p : Pattern) (selected : d135763 p = 0) : d137136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135478 q = 0) : d136903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135478, d136903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11595 q selected
    | true =>
      simp only [d135478, d136903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135759 q = 0) : d137132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135759, d137132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135759, d137132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135760 q = 0) : d137133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135760, d137133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135760, d137133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135761 q = 0) : d137134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135761, d137134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135761, d137134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135762 q = 0) : d137135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135762, d137135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135762, d137135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135763 q = 0) : d137136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135763, d137136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135763, d137136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11647 (p : Pattern) (selected : d135769 p = 0) : d137142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135629 q = 0) : d137028 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135629, d137028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135629, d137028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11621 q selected
  have h2 (q : Pattern) (selected : d135630 q = 0) : d137029 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135630, d137029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135630, d137029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135636 q = 0) : d137035 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135636, d137035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11621 q selected
    | true =>
      simp only [d135636, d137035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11622 q selected
  have h4 (q : Pattern) (selected : d135637 q = 0) : d137036 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135637, d137036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135637, d137036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135638 q = 0) : d137037 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135638, d137037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135638, d137037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135707 q = 0) : d137092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135707, d137092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11630 q selected
    | true =>
      simp only [d135707, d137092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11636 q selected
  have h7 (q : Pattern) (selected : d135709 q = 0) : d137094 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135709, d137094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11637 q selected
    | true =>
      simp only [d135709, d137094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11599 q selected
  have h8 (q : Pattern) (selected : d135710 q = 0) : d137095 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135710, d137095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135710, d137095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135711 q = 0) : d137096 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135711, d137096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135711, d137096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d135712 q = 0) : d137097 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135712, d137097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135712, d137097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135716 q = 0) : d137101 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135716, d137101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135716, d137101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11638 q selected
  have h12 (q : Pattern) (selected : d135718 q = 0) : d137103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135718, d137103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135718, d137103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11639 q selected
  have h13 (q : Pattern) (selected : d135719 q = 0) : d137104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135719, d137104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135719, d137104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135720 q = 0) : d137105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135720, d137105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d135720, d137105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d135721 q = 0) : d137106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135721, d137106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d135721, d137106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d135722 q = 0) : d137107 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135722, d137107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135722, d137107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d135758 q = 0) : d137131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135758, d137131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135758, d137131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11645 q selected
  have h18 (q : Pattern) (selected : d135764 q = 0) : d137137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135764, d137137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135764, d137137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11646 q selected
  have h19 (q : Pattern) (selected : d135765 q = 0) : d137138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135765, d137138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d135765, d137138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d135766 q = 0) : d137139 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135766, d137139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d135766, d137139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d135767 q = 0) : d137140 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135767, d137140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d135767, d137140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d135768 q = 0) : d137141 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135768, d137141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d135768, d137141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d135769 q = 0) : d137142 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d135769, d137142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d135769, d137142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11648 (p : Pattern) (selected : d135775 p = 0) : d137148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135770 q = 0) : d137143 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d135770, d137143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135770, d137143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11647 q selected
  have h2 (q : Pattern) (selected : d135771 q = 0) : d137144 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d135771, d137144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135771, d137144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135772 q = 0) : d137145 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d135772, d137145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135772, d137145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135773 q = 0) : d137146 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d135773, d137146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135773, d137146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135774 q = 0) : d137147 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d135774, d137147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135774, d137147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135775 q = 0) : d137148 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d135775, d137148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135775, d137148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11649 (p : Pattern) (selected : d135784 p = 0) : d137157 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135777 q = 0) : d137150 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135777, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135777, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6077 q selected
  have h2 (q : Pattern) (selected : d135778 q = 0) : d137151 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135778, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135778, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135779 q = 0) : d137152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6078 q selected
  have h4 (q : Pattern) (selected : d135780 q = 0) : d137153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135781 q = 0) : d137154 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135781, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135781, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135782 q = 0) : d137155 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135782, d137155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135782, d137155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135783 q = 0) : d137156 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135783, d137156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135783, d137156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135784 q = 0) : d137157 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135784, d137157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135784, d137157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11650 (p : Pattern) (selected : d135788 p = 0) : d137161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135779 q = 0) : d137152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6078 q selected
  have h2 (q : Pattern) (selected : d135780 q = 0) : d137153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135782 q = 0) : d137155 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135782, d137155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135782, d137155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135787 q = 0) : d137160 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135787, d137160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135787, d137160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135788 q = 0) : d137161 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135788, d137161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135788, d137161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11651 (p : Pattern) (selected : d135794 p = 0) : d137167 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135791 q = 0) : d137164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135792 q = 0) : d137165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135792, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135792, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135793 q = 0) : d137166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135793, d137166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135793, d137166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135794 q = 0) : d137167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135794, d137167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135794, d137167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11652 (p : Pattern) (selected : d135798 p = 0) : d137171 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135795 q = 0) : d137168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135796 q = 0) : d137169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135796, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135796, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135797 q = 0) : d137170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135797, d137170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135797, d137170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135798 q = 0) : d137171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135798, d137171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135798, d137171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11653 (p : Pattern) (selected : d135804 p = 0) : d137177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135799 q = 0) : d137172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135799, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11651 q selected
    | true =>
      simp only [d135799, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11652 q selected
  have h2 (q : Pattern) (selected : d135800 q = 0) : d137173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135800, d137173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135800, d137173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135801 q = 0) : d137174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135801, d137174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135801, d137174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135802 q = 0) : d137175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135802, d137175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135802, d137175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135803 q = 0) : d137176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135803, d137176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135803, d137176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135804 q = 0) : d137177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135804, d137177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135804, d137177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11654 (p : Pattern) (selected : d135807 p = 0) : d137180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135791 q = 0) : d137164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135792 q = 0) : d137165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135792, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135792, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135793 q = 0) : d137166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135793, d137166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135793, d137166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135807 q = 0) : d137180 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135807, d137180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135807, d137180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11655 (p : Pattern) (selected : d135808 p = 0) : d137181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135795 q = 0) : d137168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135796 q = 0) : d137169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135796, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135796, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135797 q = 0) : d137170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135797, d137170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135797, d137170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135808 q = 0) : d137181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135808, d137181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135808, d137181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11656 (p : Pattern) (selected : d135814 p = 0) : d137187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135799 q = 0) : d137172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135799, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11651 q selected
    | true =>
      simp only [d135799, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11652 q selected
  have h2 (q : Pattern) (selected : d135800 q = 0) : d137173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135800, d137173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135800, d137173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135801 q = 0) : d137174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135801, d137174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135801, d137174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135802 q = 0) : d137175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135802, d137175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135802, d137175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135803 q = 0) : d137176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135803, d137176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135803, d137176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135809 q = 0) : d137182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135809, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11654 q selected
    | true =>
      simp only [d135809, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11655 q selected
  have h7 (q : Pattern) (selected : d135810 q = 0) : d137183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135810, d137183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135810, d137183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135811 q = 0) : d137184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135811, d137184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135811, d137184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135812 q = 0) : d137185 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135812, d137185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135812, d137185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135813 q = 0) : d137186 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135813, d137186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135813, d137186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135814 q = 0) : d137187 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135814, d137187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135814, d137187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11657 (p : Pattern) (selected : d135819 p = 0) : d137192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135791 q = 0) : d137164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135792 q = 0) : d137165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135792, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135792, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135818 q = 0) : d137191 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135818, d137191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135818, d137191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135819 q = 0) : d137192 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135819, d137192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135819, d137192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11658 (p : Pattern) (selected : d135821 p = 0) : d137194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135795 q = 0) : d137168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135796 q = 0) : d137169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135796, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135796, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135820 q = 0) : d137193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135820, d137193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135820, d137193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135821 q = 0) : d137194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135821, d137194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135821, d137194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11659 (p : Pattern) (selected : d135828 p = 0) : d137201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135791 q = 0) : d137164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135826 q = 0) : d137199 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135826, d137199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135826, d137199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135827 q = 0) : d137200 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135827, d137200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135827, d137200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135828 q = 0) : d137201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135828, d137201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135828, d137201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11660 (p : Pattern) (selected : d135831 p = 0) : d137204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135795 q = 0) : d137168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135829 q = 0) : d137202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135829, d137202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135829, d137202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135830 q = 0) : d137203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135830, d137203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135830, d137203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135831 q = 0) : d137204 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135831, d137204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135831, d137204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11661 (p : Pattern) (selected : d135839 p = 0) : d137212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135835 q = 0) : d137208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135835, d137208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135835, d137208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6091 q selected
  have h2 (q : Pattern) (selected : d135836 q = 0) : d137209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135836, d137209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135836, d137209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135777 q = 0) : d137150 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135777, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135777, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6077 q selected
  have h4 (q : Pattern) (selected : d135778 q = 0) : d137151 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135778, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135778, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135837 q = 0) : d137210 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135837, d137210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135837, d137210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135779 q = 0) : d137152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6078 q selected
  have h7 (q : Pattern) (selected : d135780 q = 0) : d137153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135781 q = 0) : d137154 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135781, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135781, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135838 q = 0) : d137211 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135838, d137211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135838, d137211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135839 q = 0) : d137212 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135839, d137212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135839, d137212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11662 (p : Pattern) (selected : d135845 p = 0) : d137218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135840 q = 0) : d137213 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135840, d137213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11661 q selected
    | true =>
      simp only [d135840, d137213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135841 q = 0) : d137214 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135841, d137214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135841, d137214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135842 q = 0) : d137215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135842, d137215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135842, d137215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135843 q = 0) : d137216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135843, d137216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135843, d137216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135844 q = 0) : d137217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135844, d137217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135844, d137217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135845 q = 0) : d137218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135845, d137218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135845, d137218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11663 (p : Pattern) (selected : d135854 p = 0) : d137157 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135847 q = 0) : d137150 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135847, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135847, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6096 q selected
  have h2 (q : Pattern) (selected : d135848 q = 0) : d137151 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135848, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135848, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135849 q = 0) : d137152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135849, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135849, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6097 q selected
  have h4 (q : Pattern) (selected : d135850 q = 0) : d137153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135850, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135850, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135851 q = 0) : d137154 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135851, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135851, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135852 q = 0) : d137155 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135852, d137155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135852, d137155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135853 q = 0) : d137156 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135853, d137156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135853, d137156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135854 q = 0) : d137157 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135854, d137157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135854, d137157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11664 (p : Pattern) (selected : d135858 p = 0) : d137161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135849 q = 0) : d137152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135849, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135849, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6097 q selected
  have h2 (q : Pattern) (selected : d135850 q = 0) : d137153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135850, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135850, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135852 q = 0) : d137155 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135852, d137155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135852, d137155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135857 q = 0) : d137160 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135857, d137160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135857, d137160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135858 q = 0) : d137161 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135858, d137161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135858, d137161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11665 (p : Pattern) (selected : d135864 p = 0) : d137167 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135855 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135855, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11663 q selected
    | true =>
      simp only [d135855, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135856 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135856, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135856, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135859 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135859, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11664 q selected
    | true =>
      simp only [d135859, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135860 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135860, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135860, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135861 q = 0) : d137164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135861, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135861, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135862 q = 0) : d137165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135862, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135862, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135863 q = 0) : d137166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135863, d137166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135863, d137166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135864 q = 0) : d137167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135864, d137167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135864, d137167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11666 (p : Pattern) (selected : d135868 p = 0) : d137171 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135859 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135859, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11664 q selected
    | true =>
      simp only [d135859, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135860 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135860, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135860, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135865 q = 0) : d137168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135865, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135865, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135866 q = 0) : d137169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135866, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135866, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135867 q = 0) : d137170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135867, d137170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135867, d137170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135868 q = 0) : d137171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135868, d137171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135868, d137171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11667 (p : Pattern) (selected : d5455 p = 0) : d74181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5451 q = 0) : d74177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3354 q selected
    | true =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5452 q = 0) : d74178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5453 q = 0) : d74179 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d74179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5453, d74179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5454 q = 0) : d74180 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d74180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5454, d74180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5455 q = 0) : d74181 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d74181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5455, d74181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11668 (p : Pattern) (selected : d135875 p = 0) : d137225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135777 q = 0) : d137150 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135777, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135777, d137150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6077 q selected
  have h2 (q : Pattern) (selected : d135778 q = 0) : d137151 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135778, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135778, d137151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135779 q = 0) : d137152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135779, d137152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6078 q selected
  have h4 (q : Pattern) (selected : d135780 q = 0) : d137153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135780, d137153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135781 q = 0) : d137154 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135781, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135781, d137154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135871 q = 0) : d137221 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135871, d137221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135871, d137221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11667 q selected
  have h7 (q : Pattern) (selected : d135872 q = 0) : d137222 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135872, d137222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135872, d137222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135873 q = 0) : d137223 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135873, d137223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135873, d137223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135874 q = 0) : d137224 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135874, d137224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135874, d137224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135875 q = 0) : d137225 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135875, d137225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135875, d137225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11669 (p : Pattern) (selected : d135881 p = 0) : d137231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135876 q = 0) : d137226 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135876, d137226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11668 q selected
    | true =>
      simp only [d135876, d137226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135877 q = 0) : d137227 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135877, d137227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135877, d137227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135878 q = 0) : d137228 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135878, d137228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135878, d137228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135879 q = 0) : d137229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135879, d137229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135879, d137229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135880 q = 0) : d137230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135880, d137230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135880, d137230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135881 q = 0) : d137231 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135881, d137231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135881, d137231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11670 (p : Pattern) (selected : d135887 p = 0) : d137237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135822 q = 0) : d137195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135822, d137195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11657 q selected
    | true =>
      simp only [d135822, d137195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11658 q selected
  have h2 (q : Pattern) (selected : d135823 q = 0) : d137196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135823, d137196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135823, d137196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135824 q = 0) : d137197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135824, d137197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135824, d137197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135825 q = 0) : d137198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135825, d137198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135825, d137198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135832 q = 0) : d137205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135832, d137205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11659 q selected
    | true =>
      simp only [d135832, d137205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11660 q selected
  have h6 (q : Pattern) (selected : d135833 q = 0) : d137206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135833, d137206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135833, d137206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135834 q = 0) : d137207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135834, d137207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135834, d137207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135846 q = 0) : d137219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135846, d137219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11662 q selected
    | true =>
      simp only [d135846, d137219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11651 q selected
  have h9 (q : Pattern) (selected : d135869 q = 0) : d137172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135869, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11665 q selected
    | true =>
      simp only [d135869, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11666 q selected
  have h10 (q : Pattern) (selected : d135870 q = 0) : d137220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135870, d137220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135870, d137220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135882 q = 0) : d137232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135882, d137232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11669 q selected
    | true =>
      simp only [d135882, d137232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135883 q = 0) : d137233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135883, d137233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135883, d137233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d135884 q = 0) : d137234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135884, d137234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135884, d137234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135885 q = 0) : d137235 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135885, d137235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135885, d137235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d135886 q = 0) : d137236 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135886, d137236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135886, d137236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135887 q = 0) : d137237 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135887, d137237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135887, d137237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11671 (p : Pattern) (selected : d135888 p = 0) : d137238 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135791 q = 0) : d137164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135792 q = 0) : d137165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135792, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135792, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135818 q = 0) : d137191 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135818, d137191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135818, d137191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135888 q = 0) : d137238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135888, d137238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135888, d137238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11672 (p : Pattern) (selected : d135889 p = 0) : d137239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135795 q = 0) : d137168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135796 q = 0) : d137169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135796, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135796, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135820 q = 0) : d137193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135820, d137193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135820, d137193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135889 q = 0) : d137239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135889, d137239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135889, d137239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11673 (p : Pattern) (selected : d135894 p = 0) : d137244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135791 q = 0) : d137164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135791, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135826 q = 0) : d137199 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135826, d137199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135826, d137199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135827 q = 0) : d137200 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135827, d137200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135827, d137200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135894 q = 0) : d137244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135894, d137244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135894, d137244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11674 (p : Pattern) (selected : d135895 p = 0) : d137245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135789 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11650 q selected
    | true =>
      simp only [d135789, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135790 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135790, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135795 q = 0) : d137168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135795, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135829 q = 0) : d137202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135829, d137202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135829, d137202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135830 q = 0) : d137203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135830, d137203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135830, d137203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135895 q = 0) : d137245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135895, d137245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135895, d137245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11675 (p : Pattern) (selected : d135899 p = 0) : d137249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135840 q = 0) : d137213 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135840, d137213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11661 q selected
    | true =>
      simp only [d135840, d137213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135841 q = 0) : d137214 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135841, d137214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135841, d137214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135785 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11649 q selected
    | true =>
      simp only [d135785, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135786 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135786, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135842 q = 0) : d137215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135842, d137215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135842, d137215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135843 q = 0) : d137216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135843, d137216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135843, d137216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135844 q = 0) : d137217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135844, d137217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135844, d137217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135899 q = 0) : d137249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135899, d137249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135899, d137249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11676 (p : Pattern) (selected : d135901 p = 0) : d137180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135855 q = 0) : d137158 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135855, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11663 q selected
    | true =>
      simp only [d135855, d137158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135856 q = 0) : d137159 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135856, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135856, d137159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135859 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135859, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11664 q selected
    | true =>
      simp only [d135859, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135860 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135860, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135860, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135861 q = 0) : d137164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135861, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135861, d137164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135862 q = 0) : d137165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135862, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135862, d137165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135863 q = 0) : d137166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135863, d137166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135863, d137166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135901 q = 0) : d137180 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135901, d137180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135901, d137180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11677 (p : Pattern) (selected : d135902 p = 0) : d137181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135859 q = 0) : d137162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135859, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11664 q selected
    | true =>
      simp only [d135859, d137162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135860 q = 0) : d137163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135860, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135860, d137163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135865 q = 0) : d137168 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135865, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135865, d137168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135866 q = 0) : d137169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135866, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135866, d137169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135867 q = 0) : d137170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135867, d137170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135867, d137170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135902 q = 0) : d137181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135902, d137181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135902, d137181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11678 (p : Pattern) (selected : d135905 p = 0) : d137252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135876 q = 0) : d137226 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135876, d137226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11668 q selected
    | true =>
      simp only [d135876, d137226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135877 q = 0) : d137227 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135877, d137227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135877, d137227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135878 q = 0) : d137228 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135878, d137228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135878, d137228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135879 q = 0) : d137229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135879, d137229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135879, d137229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135880 q = 0) : d137230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135880, d137230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135880, d137230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135905 q = 0) : d137252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135905, d137252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135905, d137252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11679 (p : Pattern) (selected : d135911 p = 0) : d137258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135822 q = 0) : d137195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135822, d137195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11657 q selected
    | true =>
      simp only [d135822, d137195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11658 q selected
  have h2 (q : Pattern) (selected : d135823 q = 0) : d137196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135823, d137196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135823, d137196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135824 q = 0) : d137197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135824, d137197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135824, d137197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135825 q = 0) : d137198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135825, d137198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135825, d137198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135832 q = 0) : d137205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135832, d137205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11659 q selected
    | true =>
      simp only [d135832, d137205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11660 q selected
  have h6 (q : Pattern) (selected : d135833 q = 0) : d137206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135833, d137206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135833, d137206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135834 q = 0) : d137207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135834, d137207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135834, d137207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135846 q = 0) : d137219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135846, d137219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11662 q selected
    | true =>
      simp only [d135846, d137219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11651 q selected
  have h9 (q : Pattern) (selected : d135869 q = 0) : d137172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135869, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11665 q selected
    | true =>
      simp only [d135869, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11666 q selected
  have h10 (q : Pattern) (selected : d135870 q = 0) : d137220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135870, d137220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135870, d137220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135882 q = 0) : d137232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135882, d137232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11669 q selected
    | true =>
      simp only [d135882, d137232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d135883 q = 0) : d137233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135883, d137233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135883, d137233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d135884 q = 0) : d137234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135884, d137234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135884, d137234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135885 q = 0) : d137235 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135885, d137235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135885, d137235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d135886 q = 0) : d137236 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135886, d137236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135886, d137236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135890 q = 0) : d137240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135890, d137240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11671 q selected
    | true =>
      simp only [d135890, d137240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11672 q selected
  have h17 (q : Pattern) (selected : d135891 q = 0) : d137241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135891, d137241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135891, d137241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d135892 q = 0) : d137242 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135892, d137242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d135892, d137242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d135893 q = 0) : d137243 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135893, d137243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135893, d137243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d135896 q = 0) : d137246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135896, d137246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11673 q selected
    | true =>
      simp only [d135896, d137246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11674 q selected
  have h21 (q : Pattern) (selected : d135897 q = 0) : d137247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135897, d137247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135897, d137247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d135898 q = 0) : d137248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135898, d137248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d135898, d137248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d135900 q = 0) : d137250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135900, d137250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11675 q selected
    | true =>
      simp only [d135900, d137250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11654 q selected
  have h24 (q : Pattern) (selected : d135903 q = 0) : d137182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135903, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11676 q selected
    | true =>
      simp only [d135903, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11677 q selected
  have h25 (q : Pattern) (selected : d135904 q = 0) : d137251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135904, d137251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d135904, d137251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d135906 q = 0) : d137253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135906, d137253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11678 q selected
    | true =>
      simp only [d135906, d137253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d135907 q = 0) : d137254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135907, d137254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d135907, d137254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d135908 q = 0) : d137255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135908, d137255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d135908, d137255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d135909 q = 0) : d137256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135909, d137256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d135909, d137256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d135910 q = 0) : d137257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135910, d137257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d135910, d137257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d135911 q = 0) : d137258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135911, d137258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d135911, d137258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11680 (p : Pattern) (selected : d135918 p = 0) : d137265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135799 q = 0) : d137172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135799, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11651 q selected
    | true =>
      simp only [d135799, d137172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11652 q selected
  have h2 (q : Pattern) (selected : d135800 q = 0) : d137173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135800, d137173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135800, d137173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135801 q = 0) : d137174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135801, d137174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135801, d137174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135802 q = 0) : d137175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135802, d137175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135802, d137175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135803 q = 0) : d137176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135803, d137176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135803, d137176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135913 q = 0) : d137260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135913, d137260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11652 q selected
    | true =>
      simp only [d135913, d137260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135914 q = 0) : d137261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135914, d137261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135914, d137261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135915 q = 0) : d137262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135915, d137262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135915, d137262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135916 q = 0) : d137263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135916, d137263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135916, d137263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135917 q = 0) : d137264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135917, d137264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135917, d137264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135918 q = 0) : d137265 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135918, d137265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135918, d137265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11681 (p : Pattern) (selected : d135924 p = 0) : d137271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135913 q = 0) : d137260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135913, d137260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11652 q selected
    | true =>
      simp only [d135913, d137260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135914 q = 0) : d137261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135914, d137261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135914, d137261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135915 q = 0) : d137262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135915, d137262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135915, d137262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135916 q = 0) : d137263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135916, d137263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135916, d137263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135917 q = 0) : d137264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135917, d137264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135917, d137264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135919 q = 0) : d137266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135919, d137266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11655 q selected
    | true =>
      simp only [d135919, d137266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135920 q = 0) : d137267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135920, d137267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135920, d137267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135921 q = 0) : d137268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135921, d137268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135921, d137268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135922 q = 0) : d137269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135922, d137269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135922, d137269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135923 q = 0) : d137270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135923, d137270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135923, d137270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135924 q = 0) : d137271 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135924, d137271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135924, d137271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11682 (p : Pattern) (selected : d135931 p = 0) : d137278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135900 q = 0) : d137250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135900, d137250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11675 q selected
    | true =>
      simp only [d135900, d137250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11654 q selected
  have h2 (q : Pattern) (selected : d135903 q = 0) : d137182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135903, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11676 q selected
    | true =>
      simp only [d135903, d137182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11677 q selected
  have h3 (q : Pattern) (selected : d135904 q = 0) : d137251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135904, d137251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135904, d137251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135906 q = 0) : d137253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135906, d137253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11678 q selected
    | true =>
      simp only [d135906, d137253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135907 q = 0) : d137254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135907, d137254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135907, d137254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135908 q = 0) : d137255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135908, d137255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135908, d137255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135929 q = 0) : d137276 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135929, d137276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135929, d137276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135930 q = 0) : d137277 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135930, d137277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135930, d137277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135931 q = 0) : d137278 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135931, d137278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135931, d137278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11683 (p : Pattern) (selected : d135933 p = 0) : d137280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135919 q = 0) : d137266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135919, d137266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11655 q selected
    | true =>
      simp only [d135919, d137266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135920 q = 0) : d137267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135920, d137267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135920, d137267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135921 q = 0) : d137268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135921, d137268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135921, d137268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135922 q = 0) : d137269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135922, d137269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135922, d137269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135923 q = 0) : d137270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135923, d137270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135923, d137270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135933 q = 0) : d137280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135933, d137280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135933, d137280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11684 (p : Pattern) (selected : d135948 p = 0) : d137295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135939 q = 0) : d137286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135939, d137286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135939, d137286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6118 q selected
  have h2 (q : Pattern) (selected : d135940 q = 0) : d137287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135940, d137287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135940, d137287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135941 q = 0) : d137288 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135941, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135941, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6119 q selected
  have h4 (q : Pattern) (selected : d135942 q = 0) : d137289 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135942, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135942, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135943 q = 0) : d137290 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135943, d137290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135943, d137290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135944 q = 0) : d137291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6120 q selected
  have h7 (q : Pattern) (selected : d135945 q = 0) : d137292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135946 q = 0) : d137293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135946, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135946, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135947 q = 0) : d137294 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135947, d137294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135947, d137294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135948 q = 0) : d137295 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135948, d137295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135948, d137295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11685 (p : Pattern) (selected : d135953 p = 0) : d137300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135941 q = 0) : d137288 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135941, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135941, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6119 q selected
  have h2 (q : Pattern) (selected : d135942 q = 0) : d137289 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135942, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135942, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135944 q = 0) : d137291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6120 q selected
  have h4 (q : Pattern) (selected : d135945 q = 0) : d137292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135946 q = 0) : d137293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135946, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135946, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135951 q = 0) : d137298 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135951, d137298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135951, d137298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135952 q = 0) : d137299 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135952, d137299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135952, d137299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135953 q = 0) : d137300 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135953, d137300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135953, d137300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11686 (p : Pattern) (selected : d135959 p = 0) : d137306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135949 q = 0) : d137296 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135949, d137296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11684 q selected
    | true =>
      simp only [d135949, d137296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135950 q = 0) : d137297 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135950, d137297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135950, d137297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135954 q = 0) : d137301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135954, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11685 q selected
    | true =>
      simp only [d135954, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135955 q = 0) : d137302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135955, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135955, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135956 q = 0) : d137303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135956, d137303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135956, d137303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135957 q = 0) : d137304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135957, d137304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135957, d137304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135958 q = 0) : d137305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135958, d137305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135958, d137305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135959 q = 0) : d137306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135959, d137306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135959, d137306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11687 (p : Pattern) (selected : d135961 p = 0) : d137308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135944 q = 0) : d137291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6120 q selected
  have h2 (q : Pattern) (selected : d135945 q = 0) : d137292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135951 q = 0) : d137298 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135951, d137298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135951, d137298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135960 q = 0) : d137307 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135960, d137307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135960, d137307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135961 q = 0) : d137308 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135961, d137308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135961, d137308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11688 (p : Pattern) (selected : d135967 p = 0) : d137314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135954 q = 0) : d137301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135954, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11685 q selected
    | true =>
      simp only [d135954, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135955 q = 0) : d137302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135955, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135955, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135962 q = 0) : d137309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135962, d137309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11687 q selected
    | true =>
      simp only [d135962, d137309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135963 q = 0) : d137310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135963, d137310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135963, d137310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135964 q = 0) : d137311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135964, d137311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135964, d137311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135965 q = 0) : d137312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135965, d137312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135965, d137312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135966 q = 0) : d137313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135966, d137313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135966, d137313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135967 q = 0) : d137314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135967, d137314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135967, d137314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11689 (p : Pattern) (selected : d135976 p = 0) : d137300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135969 q = 0) : d137288 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135969, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135969, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6126 q selected
  have h2 (q : Pattern) (selected : d135970 q = 0) : d137289 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135970, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135970, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135971 q = 0) : d137291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135971, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135971, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6127 q selected
  have h4 (q : Pattern) (selected : d135972 q = 0) : d137292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135972, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135972, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135973 q = 0) : d137293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135973, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135973, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135974 q = 0) : d137298 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135974, d137298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135974, d137298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135975 q = 0) : d137299 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135975, d137299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135975, d137299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135976 q = 0) : d137300 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135976, d137300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135976, d137300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11690 (p : Pattern) (selected : d135980 p = 0) : d137308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135971 q = 0) : d137291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135971, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135971, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6127 q selected
  have h2 (q : Pattern) (selected : d135972 q = 0) : d137292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135972, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135972, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135974 q = 0) : d137298 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135974, d137298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135974, d137298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135979 q = 0) : d137307 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135979, d137307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135979, d137307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135980 q = 0) : d137308 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135980, d137308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135980, d137308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11691 (p : Pattern) (selected : d135986 p = 0) : d137314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135977 q = 0) : d137301 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135977, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11689 q selected
    | true =>
      simp only [d135977, d137301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135978 q = 0) : d137302 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135978, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135978, d137302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135981 q = 0) : d137309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135981, d137309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11690 q selected
    | true =>
      simp only [d135981, d137309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135982 q = 0) : d137310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135982, d137310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135982, d137310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135983 q = 0) : d137311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135983, d137311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135983, d137311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135984 q = 0) : d137312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135984, d137312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135984, d137312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135985 q = 0) : d137313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135985, d137313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135985, d137313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135986 q = 0) : d137314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135986, d137314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135986, d137314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11692 (p : Pattern) (selected : d135990 p = 0) : d137319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135981 q = 0) : d137309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135981, d137309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11690 q selected
    | true =>
      simp only [d135981, d137309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135982 q = 0) : d137310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135982, d137310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135982, d137310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135987 q = 0) : d137316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135987, d137316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135987, d137316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135988 q = 0) : d137317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135988, d137317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135988, d137317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135989 q = 0) : d137318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135989, d137318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135989, d137318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135990 q = 0) : d137319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135990, d137319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135990, d137319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11693 (p : Pattern) (selected : d5499 p = 0) : d74225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5495 q = 0) : d74221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d74221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5495, d74221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3354 q selected
  have h2 (q : Pattern) (selected : d5451 q = 0) : d74177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3354 q selected
    | true =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5496 q = 0) : d74222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d74222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5496, d74222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5452 q = 0) : d74178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5497 q = 0) : d74223 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d74223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5497, d74223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5498 q = 0) : d74224 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d74224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5498, d74224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d5499 q = 0) : d74225 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d74225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d5499, d74225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro11694 (p : Pattern) (selected : d135997 p = 0) : d137326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135941 q = 0) : d137288 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135941, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135941, d137288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6119 q selected
  have h2 (q : Pattern) (selected : d135942 q = 0) : d137289 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135942, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135942, d137289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135944 q = 0) : d137291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135944, d137291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6120 q selected
  have h4 (q : Pattern) (selected : d135945 q = 0) : d137292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135945, d137292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135946 q = 0) : d137293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135946, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135946, d137293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135993 q = 0) : d137322 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135993, d137322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135993, d137322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11693 q selected
  have h7 (q : Pattern) (selected : d135994 q = 0) : d137323 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135994, d137323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135994, d137323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135995 q = 0) : d137324 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135995, d137324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135995, d137324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135996 q = 0) : d137325 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135996, d137325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135996, d137325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135997 q = 0) : d137326 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135997, d137326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135997, d137326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11695 (p : Pattern) (selected : d136003 p = 0) : d137332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135998 q = 0) : d137327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135998, d137327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11694 q selected
    | true =>
      simp only [d135998, d137327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135999 q = 0) : d137328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135999, d137328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135999, d137328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136000 q = 0) : d137329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136000, d137329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136000, d137329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136001 q = 0) : d137330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136001, d137330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136001, d137330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136002 q = 0) : d137331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136002, d137331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136002, d137331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136003 q = 0) : d137332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136003, d137332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136003, d137332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11696 (p : Pattern) (selected : d136009 p = 0) : d137338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135968 q = 0) : d137315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135968, d137315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11686 q selected
    | true =>
      simp only [d135968, d137315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11688 q selected
  have h2 (q : Pattern) (selected : d135991 q = 0) : d137320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135991, d137320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11691 q selected
    | true =>
      simp only [d135991, d137320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11692 q selected
  have h3 (q : Pattern) (selected : d135992 q = 0) : d137321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135992, d137321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135992, d137321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136004 q = 0) : d137333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136004, d137333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11695 q selected
    | true =>
      simp only [d136004, d137333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136005 q = 0) : d137334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136005, d137334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136005, d137334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136006 q = 0) : d137335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136006, d137335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136006, d137335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136007 q = 0) : d137336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136007, d137336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136007, d137336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136008 q = 0) : d137337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136008, d137337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136008, d137337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136009 q = 0) : d137338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136009, d137338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136009, d137338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11697 (p : Pattern) (selected : d136014 p = 0) : d137319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135962 q = 0) : d137309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135962, d137309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11687 q selected
    | true =>
      simp only [d135962, d137309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135963 q = 0) : d137310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135963, d137310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135963, d137310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136011 q = 0) : d137316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136011, d137316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136011, d137316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136012 q = 0) : d137317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136012, d137317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136012, d137317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136013 q = 0) : d137318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136013, d137318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136013, d137318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136014 q = 0) : d137319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136014, d137319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136014, d137319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11698 (p : Pattern) (selected : d136020 p = 0) : d137345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136015 q = 0) : d137340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136015, d137340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11697 q selected
    | true =>
      simp only [d136015, d137340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136016 q = 0) : d137341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136016, d137341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136016, d137341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136017 q = 0) : d137342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136017, d137342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136017, d137342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136018 q = 0) : d137343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136018, d137343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136018, d137343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136019 q = 0) : d137344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136019, d137344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136019, d137344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136020 q = 0) : d137345 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136020, d137345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136020, d137345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11699 (p : Pattern) (selected : d136026 p = 0) : d137351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d135805 q = 0) : d137178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135805, d137178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135805, d137178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11653 q selected
  have h2 (q : Pattern) (selected : d135806 q = 0) : d137179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135806, d137179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135806, d137179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135815 q = 0) : d137188 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135815, d137188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11653 q selected
    | true =>
      simp only [d135815, d137188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11656 q selected
  have h4 (q : Pattern) (selected : d135816 q = 0) : d137189 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135816, d137189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135816, d137189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135817 q = 0) : d137190 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135817, d137190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135817, d137190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135912 q = 0) : d137259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135912, d137259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11670 q selected
    | true =>
      simp only [d135912, d137259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11679 q selected
  have h7 (q : Pattern) (selected : d135925 q = 0) : d137272 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135925, d137272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11680 q selected
    | true =>
      simp only [d135925, d137272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11681 q selected
  have h8 (q : Pattern) (selected : d135926 q = 0) : d137273 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135926, d137273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135926, d137273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135927 q = 0) : d137274 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135927, d137274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135927, d137274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d135928 q = 0) : d137275 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135928, d137275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135928, d137275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d135932 q = 0) : d137279 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135932, d137279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135932, d137279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11682 q selected
  have h12 (q : Pattern) (selected : d135934 q = 0) : d137281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135934, d137281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135934, d137281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11683 q selected
  have h13 (q : Pattern) (selected : d135935 q = 0) : d137282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135935, d137282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135935, d137282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135936 q = 0) : d137283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135936, d137283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d135936, d137283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d135937 q = 0) : d137284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135937, d137284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d135937, d137284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d135938 q = 0) : d137285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135938, d137285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135938, d137285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d136010 q = 0) : d137339 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136010, d137339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136010, d137339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11696 q selected
  have h18 (q : Pattern) (selected : d136021 q = 0) : d137346 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136021, d137346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136021, d137346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11698 q selected
  have h19 (q : Pattern) (selected : d136022 q = 0) : d137347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136022, d137347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136022, d137347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d136023 q = 0) : d137348 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136023, d137348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d136023, d137348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d136024 q = 0) : d137349 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136024, d137349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d136024, d137349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d136025 q = 0) : d137350 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136025, d137350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d136025, d137350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d136026 q = 0) : d137351 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136026, d137351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d136026, d137351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11700 (p : Pattern) (selected : d136032 p = 0) : d137357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136027 q = 0) : d137352 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136027, d137352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136027, d137352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11699 q selected
  have h2 (q : Pattern) (selected : d136028 q = 0) : d137353 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136028, d137353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136028, d137353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136029 q = 0) : d137354 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136029, d137354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136029, d137354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136030 q = 0) : d137355 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136030, d137355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136030, d137355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136031 q = 0) : d137356 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136031, d137356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136031, d137356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136032 q = 0) : d137357 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d136032, d137357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136032, d137357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11701 (p : Pattern) (selected : d136042 p = 0) : d137367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136035 q = 0) : d137360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6139 q selected
  have h2 (q : Pattern) (selected : d136036 q = 0) : d137361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136037 q = 0) : d137362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6140 q selected
  have h4 (q : Pattern) (selected : d136038 q = 0) : d137363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136039 q = 0) : d137364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136039, d137364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136039, d137364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136040 q = 0) : d137365 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136040, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136040, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136041 q = 0) : d137366 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136041, d137366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136041, d137366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136042 q = 0) : d137367 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136042, d137367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136042, d137367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11702 (p : Pattern) (selected : d136046 p = 0) : d137371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136037 q = 0) : d137362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6140 q selected
  have h2 (q : Pattern) (selected : d136038 q = 0) : d137363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136040 q = 0) : d137365 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136040, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136040, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136045 q = 0) : d137370 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136045, d137370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136045, d137370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136046 q = 0) : d137371 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136046, d137371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136046, d137371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11703 (p : Pattern) (selected : d136052 p = 0) : d137377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136043 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11701 q selected
    | true =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136044 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136049 q = 0) : d137374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136050 q = 0) : d137375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136050, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136050, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136051 q = 0) : d137376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136051, d137376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136051, d137376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136052 q = 0) : d137377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136052, d137377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136052, d137377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11704 (p : Pattern) (selected : d136056 p = 0) : d137381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136053 q = 0) : d137378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136054 q = 0) : d137379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136054, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136054, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136055 q = 0) : d137380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136055, d137380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136055, d137380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136056 q = 0) : d137381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136056, d137381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136056, d137381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11705 (p : Pattern) (selected : d136062 p = 0) : d137387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136057 q = 0) : d137382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136057, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11703 q selected
    | true =>
      simp only [d136057, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
  have h2 (q : Pattern) (selected : d136058 q = 0) : d137383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136058, d137383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136058, d137383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136059 q = 0) : d137384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136059, d137384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136059, d137384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136060 q = 0) : d137385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136060, d137385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136060, d137385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136061 q = 0) : d137386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136061, d137386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136061, d137386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136062 q = 0) : d137387 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136062, d137387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136062, d137387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11706 (p : Pattern) (selected : d136065 p = 0) : d137390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136043 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11701 q selected
    | true =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136044 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136049 q = 0) : d137374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136050 q = 0) : d137375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136050, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136050, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136051 q = 0) : d137376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136051, d137376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136051, d137376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136065 q = 0) : d137390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136065, d137390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136065, d137390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11707 (p : Pattern) (selected : d136066 p = 0) : d137391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136053 q = 0) : d137378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136054 q = 0) : d137379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136054, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136054, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136055 q = 0) : d137380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136055, d137380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136055, d137380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136066 q = 0) : d137391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136066, d137391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136066, d137391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11708 (p : Pattern) (selected : d136072 p = 0) : d137397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136057 q = 0) : d137382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136057, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11703 q selected
    | true =>
      simp only [d136057, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
  have h2 (q : Pattern) (selected : d136058 q = 0) : d137383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136058, d137383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136058, d137383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136059 q = 0) : d137384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136059, d137384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136059, d137384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136060 q = 0) : d137385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136060, d137385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136060, d137385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136061 q = 0) : d137386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136061, d137386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136061, d137386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136067 q = 0) : d137392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136067, d137392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11706 q selected
    | true =>
      simp only [d136067, d137392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11707 q selected
  have h7 (q : Pattern) (selected : d136068 q = 0) : d137393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136068, d137393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136068, d137393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136069 q = 0) : d137394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136069, d137394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136069, d137394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136070 q = 0) : d137395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136070, d137395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136070, d137395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136071 q = 0) : d137396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136071, d137396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136071, d137396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136072 q = 0) : d137397 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136072, d137397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136072, d137397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11709 (p : Pattern) (selected : d136077 p = 0) : d137402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136043 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11701 q selected
    | true =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136044 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136049 q = 0) : d137374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136050 q = 0) : d137375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136050, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136050, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136076 q = 0) : d137401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136076, d137401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136076, d137401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136077 q = 0) : d137402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136077, d137402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136077, d137402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11710 (p : Pattern) (selected : d136079 p = 0) : d137404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136053 q = 0) : d137378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136054 q = 0) : d137379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136054, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136054, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136078 q = 0) : d137403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136078, d137403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136078, d137403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136079 q = 0) : d137404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136079, d137404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136079, d137404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11711 (p : Pattern) (selected : d136086 p = 0) : d137411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136043 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11701 q selected
    | true =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136044 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136049 q = 0) : d137374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136084 q = 0) : d137409 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136084, d137409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136084, d137409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136085 q = 0) : d137410 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136085, d137410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136085, d137410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136086 q = 0) : d137411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136086, d137411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136086, d137411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11712 (p : Pattern) (selected : d136089 p = 0) : d137414 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136053 q = 0) : d137378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136087 q = 0) : d137412 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136087, d137412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136087, d137412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136088 q = 0) : d137413 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136088, d137413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136088, d137413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136089 q = 0) : d137414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136089, d137414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136089, d137414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11713 (p : Pattern) (selected : d136097 p = 0) : d137422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136093 q = 0) : d137418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136093, d137418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136093, d137418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6154 q selected
  have h2 (q : Pattern) (selected : d136094 q = 0) : d137419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136094, d137419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136094, d137419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136035 q = 0) : d137360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6139 q selected
  have h4 (q : Pattern) (selected : d136036 q = 0) : d137361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136095 q = 0) : d137420 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136095, d137420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136095, d137420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136037 q = 0) : d137362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6140 q selected
  have h7 (q : Pattern) (selected : d136038 q = 0) : d137363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136039 q = 0) : d137364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136039, d137364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136039, d137364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136096 q = 0) : d137421 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136096, d137421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136096, d137421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136097 q = 0) : d137422 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136097, d137422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136097, d137422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11714 (p : Pattern) (selected : d136103 p = 0) : d137428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136098 q = 0) : d137423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136098, d137423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11713 q selected
    | true =>
      simp only [d136098, d137423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136099 q = 0) : d137424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136099, d137424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136099, d137424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136043 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11701 q selected
    | true =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136044 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136100 q = 0) : d137425 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136100, d137425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136100, d137425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136101 q = 0) : d137426 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136101, d137426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136101, d137426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136102 q = 0) : d137427 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136102, d137427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136102, d137427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136103 q = 0) : d137428 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136103, d137428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136103, d137428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11715 (p : Pattern) (selected : d136112 p = 0) : d137367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136105 q = 0) : d137360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136105, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136105, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6159 q selected
  have h2 (q : Pattern) (selected : d136106 q = 0) : d137361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136106, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136106, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136107 q = 0) : d137362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136107, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136107, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6160 q selected
  have h4 (q : Pattern) (selected : d136108 q = 0) : d137363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136108, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136108, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136109 q = 0) : d137364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136109, d137364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136109, d137364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136110 q = 0) : d137365 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136110, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136110, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136111 q = 0) : d137366 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136111, d137366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136111, d137366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136112 q = 0) : d137367 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136112, d137367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136112, d137367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11716 (p : Pattern) (selected : d136116 p = 0) : d137371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136107 q = 0) : d137362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136107, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136107, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6160 q selected
  have h2 (q : Pattern) (selected : d136108 q = 0) : d137363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136108, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136108, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136110 q = 0) : d137365 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136110, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136110, d137365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136115 q = 0) : d137370 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136115, d137370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136115, d137370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136116 q = 0) : d137371 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136116, d137371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136116, d137371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11717 (p : Pattern) (selected : d136122 p = 0) : d137377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136113 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136113, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11715 q selected
    | true =>
      simp only [d136113, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136114 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136114, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136114, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136117 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11716 q selected
    | true =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136118 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136119 q = 0) : d137374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136119, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136119, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136120 q = 0) : d137375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136120, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136120, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136121 q = 0) : d137376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136121, d137376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136121, d137376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136122 q = 0) : d137377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136122, d137377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136122, d137377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11718 (p : Pattern) (selected : d136126 p = 0) : d137381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136117 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11716 q selected
    | true =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136118 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136123 q = 0) : d137378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136123, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136123, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136124 q = 0) : d137379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136124, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136124, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136125 q = 0) : d137380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136125, d137380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136125, d137380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136126 q = 0) : d137381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136126, d137381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136126, d137381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11719 (p : Pattern) (selected : d5544 p = 0) : d74270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5540 q = 0) : d74266 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d74266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3370 q selected
    | true =>
      simp only [d5540, d74266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5541 q = 0) : d74267 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d74267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5541, d74267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5542 q = 0) : d74268 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5542, d74268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5542, d74268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5543 q = 0) : d74269 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5543, d74269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5543, d74269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5544 q = 0) : d74270 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5544, d74270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5544, d74270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11720 (p : Pattern) (selected : d136133 p = 0) : d137435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136035 q = 0) : d137360 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136035, d137360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6139 q selected
  have h2 (q : Pattern) (selected : d136036 q = 0) : d137361 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136036, d137361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136037 q = 0) : d137362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136037, d137362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6140 q selected
  have h4 (q : Pattern) (selected : d136038 q = 0) : d137363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136038, d137363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136039 q = 0) : d137364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136039, d137364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136039, d137364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136129 q = 0) : d137431 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136129, d137431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136129, d137431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11719 q selected
  have h7 (q : Pattern) (selected : d136130 q = 0) : d137432 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136130, d137432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136130, d137432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136131 q = 0) : d137433 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136131, d137433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136131, d137433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136132 q = 0) : d137434 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136132, d137434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136132, d137434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136133 q = 0) : d137435 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136133, d137435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136133, d137435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11721 (p : Pattern) (selected : d136139 p = 0) : d137441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136134 q = 0) : d137436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136134, d137436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11720 q selected
    | true =>
      simp only [d136134, d137436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136135 q = 0) : d137437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136135, d137437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136135, d137437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136136 q = 0) : d137438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136136, d137438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136136, d137438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136137 q = 0) : d137439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136137, d137439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136137, d137439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136138 q = 0) : d137440 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136138, d137440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136138, d137440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136139 q = 0) : d137441 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136139, d137441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136139, d137441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11722 (p : Pattern) (selected : d136145 p = 0) : d137447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136080 q = 0) : d137405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136080, d137405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11709 q selected
    | true =>
      simp only [d136080, d137405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11710 q selected
  have h2 (q : Pattern) (selected : d136081 q = 0) : d137406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136081, d137406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136081, d137406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136082 q = 0) : d137407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136082, d137407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136082, d137407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136083 q = 0) : d137408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136083, d137408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136083, d137408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136090 q = 0) : d137415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136090, d137415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11711 q selected
    | true =>
      simp only [d136090, d137415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11712 q selected
  have h6 (q : Pattern) (selected : d136091 q = 0) : d137416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136091, d137416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136091, d137416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136092 q = 0) : d137417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136092, d137417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136092, d137417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136104 q = 0) : d137429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136104, d137429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11714 q selected
    | true =>
      simp only [d136104, d137429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11703 q selected
  have h9 (q : Pattern) (selected : d136127 q = 0) : d137382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136127, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11717 q selected
    | true =>
      simp only [d136127, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11718 q selected
  have h10 (q : Pattern) (selected : d136128 q = 0) : d137430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136128, d137430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136128, d137430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136140 q = 0) : d137442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136140, d137442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11721 q selected
    | true =>
      simp only [d136140, d137442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d136141 q = 0) : d137443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136141, d137443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136141, d137443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d136142 q = 0) : d137444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136142, d137444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136142, d137444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136143 q = 0) : d137445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136143, d137445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136143, d137445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d136144 q = 0) : d137446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136144, d137446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136144, d137446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136145 q = 0) : d137447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136145, d137447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136145, d137447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11723 (p : Pattern) (selected : d136146 p = 0) : d137448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136043 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11701 q selected
    | true =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136044 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136049 q = 0) : d137374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136050 q = 0) : d137375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136050, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136050, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136076 q = 0) : d137401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136076, d137401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136076, d137401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136146 q = 0) : d137448 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136146, d137448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136146, d137448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11724 (p : Pattern) (selected : d136147 p = 0) : d137449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136053 q = 0) : d137378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136054 q = 0) : d137379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136054, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136054, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136078 q = 0) : d137403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136078, d137403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136078, d137403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136147 q = 0) : d137449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136147, d137449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136147, d137449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11725 (p : Pattern) (selected : d136152 p = 0) : d137454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136043 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11701 q selected
    | true =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136044 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136049 q = 0) : d137374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136049, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136084 q = 0) : d137409 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136084, d137409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136084, d137409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136085 q = 0) : d137410 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136085, d137410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136085, d137410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136152 q = 0) : d137454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136152, d137454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136152, d137454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11726 (p : Pattern) (selected : d136153 p = 0) : d137455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136047 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11702 q selected
    | true =>
      simp only [d136047, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136048 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136048, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136053 q = 0) : d137378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136053, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136087 q = 0) : d137412 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136087, d137412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136087, d137412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136088 q = 0) : d137413 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136088, d137413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136088, d137413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136153 q = 0) : d137455 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136153, d137455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136153, d137455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11727 (p : Pattern) (selected : d136157 p = 0) : d137459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136098 q = 0) : d137423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136098, d137423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11713 q selected
    | true =>
      simp only [d136098, d137423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136099 q = 0) : d137424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136099, d137424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136099, d137424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136043 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11701 q selected
    | true =>
      simp only [d136043, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136044 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136044, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136100 q = 0) : d137425 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136100, d137425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136100, d137425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136101 q = 0) : d137426 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136101, d137426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136101, d137426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136102 q = 0) : d137427 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136102, d137427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136102, d137427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136157 q = 0) : d137459 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136157, d137459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136157, d137459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11728 (p : Pattern) (selected : d136159 p = 0) : d137390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136113 q = 0) : d137368 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136113, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11715 q selected
    | true =>
      simp only [d136113, d137368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136114 q = 0) : d137369 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136114, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136114, d137369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136117 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11716 q selected
    | true =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136118 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136119 q = 0) : d137374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136119, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136119, d137374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136120 q = 0) : d137375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136120, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136120, d137375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136121 q = 0) : d137376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136121, d137376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136121, d137376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136159 q = 0) : d137390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136159, d137390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136159, d137390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11729 (p : Pattern) (selected : d136160 p = 0) : d137391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136117 q = 0) : d137372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11716 q selected
    | true =>
      simp only [d136117, d137372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136118 q = 0) : d137373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, d137373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136123 q = 0) : d137378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136123, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136123, d137378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136124 q = 0) : d137379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136124, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136124, d137379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136125 q = 0) : d137380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136125, d137380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136125, d137380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136160 q = 0) : d137391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136160, d137391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136160, d137391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11730 (p : Pattern) (selected : d136163 p = 0) : d137462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136134 q = 0) : d137436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136134, d137436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11720 q selected
    | true =>
      simp only [d136134, d137436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136135 q = 0) : d137437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136135, d137437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136135, d137437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136136 q = 0) : d137438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136136, d137438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136136, d137438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136137 q = 0) : d137439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136137, d137439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136137, d137439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136138 q = 0) : d137440 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136138, d137440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136138, d137440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136163 q = 0) : d137462 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136163, d137462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136163, d137462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11731 (p : Pattern) (selected : d136169 p = 0) : d137468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136080 q = 0) : d137405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136080, d137405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11709 q selected
    | true =>
      simp only [d136080, d137405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11710 q selected
  have h2 (q : Pattern) (selected : d136081 q = 0) : d137406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136081, d137406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136081, d137406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136082 q = 0) : d137407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136082, d137407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136082, d137407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136083 q = 0) : d137408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136083, d137408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136083, d137408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136090 q = 0) : d137415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136090, d137415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11711 q selected
    | true =>
      simp only [d136090, d137415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11712 q selected
  have h6 (q : Pattern) (selected : d136091 q = 0) : d137416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136091, d137416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136091, d137416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136092 q = 0) : d137417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136092, d137417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136092, d137417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136104 q = 0) : d137429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136104, d137429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11714 q selected
    | true =>
      simp only [d136104, d137429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11703 q selected
  have h9 (q : Pattern) (selected : d136127 q = 0) : d137382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136127, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11717 q selected
    | true =>
      simp only [d136127, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11718 q selected
  have h10 (q : Pattern) (selected : d136128 q = 0) : d137430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136128, d137430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136128, d137430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136140 q = 0) : d137442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136140, d137442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11721 q selected
    | true =>
      simp only [d136140, d137442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d136141 q = 0) : d137443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136141, d137443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136141, d137443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d136142 q = 0) : d137444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136142, d137444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136142, d137444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136143 q = 0) : d137445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136143, d137445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136143, d137445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d136144 q = 0) : d137446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136144, d137446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136144, d137446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136148 q = 0) : d137450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136148, d137450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11723 q selected
    | true =>
      simp only [d136148, d137450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11724 q selected
  have h17 (q : Pattern) (selected : d136149 q = 0) : d137451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136149, d137451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136149, d137451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d136150 q = 0) : d137452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136150, d137452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136150, d137452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d136151 q = 0) : d137453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136151, d137453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136151, d137453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d136154 q = 0) : d137456 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136154, d137456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11725 q selected
    | true =>
      simp only [d136154, d137456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11726 q selected
  have h21 (q : Pattern) (selected : d136155 q = 0) : d137457 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136155, d137457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136155, d137457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d136156 q = 0) : d137458 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136156, d137458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d136156, d137458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d136158 q = 0) : d137460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136158, d137460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11727 q selected
    | true =>
      simp only [d136158, d137460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11706 q selected
  have h24 (q : Pattern) (selected : d136161 q = 0) : d137392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136161, d137392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11728 q selected
    | true =>
      simp only [d136161, d137392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11729 q selected
  have h25 (q : Pattern) (selected : d136162 q = 0) : d137461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136162, d137461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d136162, d137461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d136164 q = 0) : d137463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136164, d137463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11730 q selected
    | true =>
      simp only [d136164, d137463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d136165 q = 0) : d137464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136165, d137464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d136165, d137464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d136166 q = 0) : d137465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136166, d137465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d136166, d137465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d136167 q = 0) : d137466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136167, d137466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d136167, d137466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d136168 q = 0) : d137467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136168, d137467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d136168, d137467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d136169 q = 0) : d137468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136169, d137468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136169, d137468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11732 (p : Pattern) (selected : d136176 p = 0) : d137475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136057 q = 0) : d137382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136057, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11703 q selected
    | true =>
      simp only [d136057, d137382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
  have h2 (q : Pattern) (selected : d136058 q = 0) : d137383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136058, d137383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136058, d137383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136059 q = 0) : d137384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136059, d137384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136059, d137384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136060 q = 0) : d137385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136060, d137385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136060, d137385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136061 q = 0) : d137386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136061, d137386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136061, d137386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136171 q = 0) : d137470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136171, d137470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
    | true =>
      simp only [d136171, d137470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136172 q = 0) : d137471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136172, d137471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136172, d137471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136173 q = 0) : d137472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136173, d137472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136173, d137472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136174 q = 0) : d137473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136174, d137473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136174, d137473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136175 q = 0) : d137474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136175, d137474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136175, d137474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136176 q = 0) : d137475 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136176, d137475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136176, d137475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11733 (p : Pattern) (selected : d136182 p = 0) : d137481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136171 q = 0) : d137470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136171, d137470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11704 q selected
    | true =>
      simp only [d136171, d137470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136172 q = 0) : d137471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136172, d137471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136172, d137471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136173 q = 0) : d137472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136173, d137472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136173, d137472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136174 q = 0) : d137473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136174, d137473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136174, d137473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136175 q = 0) : d137474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136175, d137474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136175, d137474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136177 q = 0) : d137476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136177, d137476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11707 q selected
    | true =>
      simp only [d136177, d137476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136178 q = 0) : d137477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136178, d137477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136178, d137477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136179 q = 0) : d137478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136179, d137478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136179, d137478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136180 q = 0) : d137479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136180, d137479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136180, d137479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136181 q = 0) : d137480 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136181, d137480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136181, d137480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136182 q = 0) : d137481 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136182, d137481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136182, d137481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11734 (p : Pattern) (selected : d136189 p = 0) : d137488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136158 q = 0) : d137460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136158, d137460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11727 q selected
    | true =>
      simp only [d136158, d137460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11706 q selected
  have h2 (q : Pattern) (selected : d136161 q = 0) : d137392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136161, d137392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11728 q selected
    | true =>
      simp only [d136161, d137392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11729 q selected
  have h3 (q : Pattern) (selected : d136162 q = 0) : d137461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136162, d137461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136162, d137461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136164 q = 0) : d137463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136164, d137463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11730 q selected
    | true =>
      simp only [d136164, d137463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136165 q = 0) : d137464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136165, d137464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136165, d137464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136166 q = 0) : d137465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136166, d137465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136166, d137465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136187 q = 0) : d137486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136187, d137486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136187, d137486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136188 q = 0) : d137487 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136188, d137487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136188, d137487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136189 q = 0) : d137488 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136189, d137488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136189, d137488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11735 (p : Pattern) (selected : d136191 p = 0) : d137490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136177 q = 0) : d137476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136177, d137476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11707 q selected
    | true =>
      simp only [d136177, d137476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136178 q = 0) : d137477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136178, d137477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136178, d137477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136179 q = 0) : d137478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136179, d137478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136179, d137478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136180 q = 0) : d137479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136180, d137479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136180, d137479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136181 q = 0) : d137480 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136181, d137480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136181, d137480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136191 q = 0) : d137490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136191, d137490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136191, d137490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11736 (p : Pattern) (selected : d136206 p = 0) : d137505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136197 q = 0) : d137496 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136197, d137496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136197, d137496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6182 q selected
  have h2 (q : Pattern) (selected : d136198 q = 0) : d137497 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136198, d137497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136198, d137497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136199 q = 0) : d137498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6183 q selected
  have h4 (q : Pattern) (selected : d136200 q = 0) : d137499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136201 q = 0) : d137500 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136201, d137500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136201, d137500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136202 q = 0) : d137501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6184 q selected
  have h7 (q : Pattern) (selected : d136203 q = 0) : d137502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136204 q = 0) : d137503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136204, d137503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136204, d137503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136205 q = 0) : d137504 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136205, d137504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136205, d137504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136206 q = 0) : d137505 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136206, d137505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136206, d137505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11737 (p : Pattern) (selected : d136211 p = 0) : d137510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136199 q = 0) : d137498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6183 q selected
  have h2 (q : Pattern) (selected : d136200 q = 0) : d137499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136202 q = 0) : d137501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6184 q selected
  have h4 (q : Pattern) (selected : d136203 q = 0) : d137502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136204 q = 0) : d137503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136204, d137503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136204, d137503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136209 q = 0) : d137508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136209, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136209, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136210 q = 0) : d137509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136210, d137509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136210, d137509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136211 q = 0) : d137510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136211, d137510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136211, d137510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11738 (p : Pattern) (selected : d136217 p = 0) : d137516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136207 q = 0) : d137506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136207, d137506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11736 q selected
    | true =>
      simp only [d136207, d137506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136208 q = 0) : d137507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136208, d137507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136208, d137507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136212 q = 0) : d137511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136212, d137511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11737 q selected
    | true =>
      simp only [d136212, d137511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136213 q = 0) : d137512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136213, d137512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136213, d137512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136214 q = 0) : d137513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136214, d137513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136214, d137513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136215 q = 0) : d137514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136215, d137514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136215, d137514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136216 q = 0) : d137515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136216, d137515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136216, d137515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136217 q = 0) : d137516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136217, d137516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136217, d137516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11739 (p : Pattern) (selected : d136219 p = 0) : d137518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136202 q = 0) : d137501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6184 q selected
  have h2 (q : Pattern) (selected : d136203 q = 0) : d137502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136209 q = 0) : d137508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136209, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136209, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136218 q = 0) : d137517 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136218, d137517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136218, d137517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136219 q = 0) : d137518 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136219, d137518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136219, d137518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11740 (p : Pattern) (selected : d136225 p = 0) : d137524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136212 q = 0) : d137511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136212, d137511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11737 q selected
    | true =>
      simp only [d136212, d137511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136213 q = 0) : d137512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136213, d137512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136213, d137512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136220 q = 0) : d137519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136220, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11739 q selected
    | true =>
      simp only [d136220, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136221 q = 0) : d137520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136221, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136221, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136222 q = 0) : d137521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136222, d137521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136222, d137521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136223 q = 0) : d137522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136223, d137522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136223, d137522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136224 q = 0) : d137523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136224, d137523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136224, d137523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136225 q = 0) : d137524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136225, d137524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136225, d137524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11741 (p : Pattern) (selected : d136234 p = 0) : d137510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136227 q = 0) : d137498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136227, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136227, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6191 q selected
  have h2 (q : Pattern) (selected : d136228 q = 0) : d137499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136228, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136228, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136229 q = 0) : d137501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136229, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136229, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6192 q selected
  have h4 (q : Pattern) (selected : d136230 q = 0) : d137502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136230, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136230, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136231 q = 0) : d137503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136231, d137503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136231, d137503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136232 q = 0) : d137508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136232, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136232, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136233 q = 0) : d137509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136233, d137509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136233, d137509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136234 q = 0) : d137510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136234, d137510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136234, d137510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11742 (p : Pattern) (selected : d136238 p = 0) : d137518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136229 q = 0) : d137501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136229, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136229, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6192 q selected
  have h2 (q : Pattern) (selected : d136230 q = 0) : d137502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136230, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136230, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136232 q = 0) : d137508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136232, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136232, d137508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136237 q = 0) : d137517 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136237, d137517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136237, d137517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136238 q = 0) : d137518 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136238, d137518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136238, d137518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11743 (p : Pattern) (selected : d136244 p = 0) : d137524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136235 q = 0) : d137511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136235, d137511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11741 q selected
    | true =>
      simp only [d136235, d137511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136236 q = 0) : d137512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136236, d137512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136236, d137512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136239 q = 0) : d137519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136239, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11742 q selected
    | true =>
      simp only [d136239, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136240 q = 0) : d137520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136240, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136240, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136241 q = 0) : d137521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136241, d137521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136241, d137521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136242 q = 0) : d137522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136242, d137522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136242, d137522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136243 q = 0) : d137523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136243, d137523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136243, d137523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136244 q = 0) : d137524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136244, d137524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136244, d137524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11744 (p : Pattern) (selected : d136248 p = 0) : d137529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136239 q = 0) : d137519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136239, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11742 q selected
    | true =>
      simp only [d136239, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136240 q = 0) : d137520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136240, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136240, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136245 q = 0) : d137526 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136245, d137526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136245, d137526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136246 q = 0) : d137527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136246, d137527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136246, d137527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136247 q = 0) : d137528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136247, d137528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136247, d137528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136248 q = 0) : d137529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136248, d137529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136248, d137529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11745 (p : Pattern) (selected : d5588 p = 0) : d74314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5584 q = 0) : d74310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5584, d74310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5584, d74310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3370 q selected
  have h2 (q : Pattern) (selected : d5540 q = 0) : d74266 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5540, d74266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3370 q selected
    | true =>
      simp only [d5540, d74266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5585 q = 0) : d74311 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5585, d74311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5585, d74311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5541 q = 0) : d74267 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5541, d74267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5541, d74267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5586 q = 0) : d74312 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5586, d74312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5586, d74312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5587 q = 0) : d74313 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5587, d74313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5587, d74313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d5588 q = 0) : d74314 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5588, d74314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d5588, d74314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro11746 (p : Pattern) (selected : d136255 p = 0) : d137536 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136199 q = 0) : d137498 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136199, d137498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6183 q selected
  have h2 (q : Pattern) (selected : d136200 q = 0) : d137499 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136200, d137499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136202 q = 0) : d137501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136202, d137501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6184 q selected
  have h4 (q : Pattern) (selected : d136203 q = 0) : d137502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136203, d137502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136204 q = 0) : d137503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136204, d137503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136204, d137503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136251 q = 0) : d137532 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136251, d137532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136251, d137532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11745 q selected
  have h7 (q : Pattern) (selected : d136252 q = 0) : d137533 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136252, d137533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136252, d137533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136253 q = 0) : d137534 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136253, d137534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136253, d137534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136254 q = 0) : d137535 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136254, d137535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136254, d137535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136255 q = 0) : d137536 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136255, d137536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136255, d137536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11747 (p : Pattern) (selected : d136261 p = 0) : d137542 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136256 q = 0) : d137537 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136256, d137537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11746 q selected
    | true =>
      simp only [d136256, d137537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136257 q = 0) : d137538 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136257, d137538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136257, d137538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136258 q = 0) : d137539 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136258, d137539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136258, d137539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136259 q = 0) : d137540 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136259, d137540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136259, d137540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136260 q = 0) : d137541 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136260, d137541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136260, d137541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136261 q = 0) : d137542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136261, d137542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136261, d137542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11748 (p : Pattern) (selected : d136267 p = 0) : d137548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136226 q = 0) : d137525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136226, d137525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11738 q selected
    | true =>
      simp only [d136226, d137525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11740 q selected
  have h2 (q : Pattern) (selected : d136249 q = 0) : d137530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136249, d137530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11743 q selected
    | true =>
      simp only [d136249, d137530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11744 q selected
  have h3 (q : Pattern) (selected : d136250 q = 0) : d137531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136250, d137531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136250, d137531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136262 q = 0) : d137543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136262, d137543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11747 q selected
    | true =>
      simp only [d136262, d137543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136263 q = 0) : d137544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136263, d137544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136263, d137544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136264 q = 0) : d137545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136264, d137545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136264, d137545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136265 q = 0) : d137546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136265, d137546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136265, d137546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136266 q = 0) : d137547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136266, d137547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136266, d137547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136267 q = 0) : d137548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136267, d137548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136267, d137548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11749 (p : Pattern) (selected : d136272 p = 0) : d137529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136220 q = 0) : d137519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136220, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11739 q selected
    | true =>
      simp only [d136220, d137519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136221 q = 0) : d137520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136221, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136221, d137520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136269 q = 0) : d137526 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136269, d137526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136269, d137526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136270 q = 0) : d137527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136270, d137527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136270, d137527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136271 q = 0) : d137528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136271, d137528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136271, d137528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136272 q = 0) : d137529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136272, d137529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136272, d137529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
