import NetHack.Soko22Hazard87.AndIntroBlocks0038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro9750 (p : Pattern) (ha : d70148 p = 1) (hb : d82883 p = 1) : d72150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70148 q = 1) (hb : d82878 q = 1) : d72145 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82878, d72145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9749 q ha hb
    | true =>
      simp only [d82878, d72145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70148 q = 1) (hb : d82879 q = 1) : d72146 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82879, d72146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82879, d72146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70148 q = 1) (hb : d82880 q = 1) : d72147 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82880, d72147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82880, d72147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70148 q = 1) (hb : d82881 q = 1) : d72148 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82881, d72148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82881, d72148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70148 q = 1) (hb : d82882 q = 1) : d72149 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82882, d72149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82882, d72149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70148 q = 1) (hb : d82883 q = 1) : d72150 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82883, d72150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82883, d72150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9751 (p : Pattern) (ha : d70148 p = 1) (hb : d82889 p = 1) : d72156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70148 q = 1) (hb : d82884 q = 1) : d72151 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82884, d72151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9750 q ha hb
    | true =>
      simp only [d82884, d72151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70148 q = 1) (hb : d82885 q = 1) : d72152 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82885, d72152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82885, d72152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70148 q = 1) (hb : d82886 q = 1) : d72153 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82886, d72153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82886, d72153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70148 q = 1) (hb : d82887 q = 1) : d72154 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82887, d72154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82887, d72154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70148 q = 1) (hb : d82888 q = 1) : d72155 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82888, d72155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82888, d72155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70148 q = 1) (hb : d82889 q = 1) : d72156 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82889, d72156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82889, d72156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9752 (p : Pattern) (ha : d70148 p = 1) (hb : d82895 p = 1) : d72162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70148 q = 1) (hb : d82890 q = 1) : d72157 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82890, d72157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9751 q ha hb
    | true =>
      simp only [d82890, d72157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70148 q = 1) (hb : d82891 q = 1) : d72158 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82891, d72158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82891, d72158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70148 q = 1) (hb : d82892 q = 1) : d72159 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82892, d72159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82892, d72159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70148 q = 1) (hb : d82893 q = 1) : d72160 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82893, d72160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82893, d72160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70148 q = 1) (hb : d82894 q = 1) : d72161 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82894, d72161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82894, d72161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70148 q = 1) (hb : d82895 q = 1) : d72162 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82895, d72162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82895, d72162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9753 (p : Pattern) (ha : d70148 p = 1) (hb : d82901 p = 1) : d72168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70148 q = 1) (hb : d82896 q = 1) : d72163 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82896, d72163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9752 q ha hb
    | true =>
      simp only [d82896, d72163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70148 q = 1) (hb : d82897 q = 1) : d72164 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82897, d72164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82897, d72164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70148 q = 1) (hb : d82898 q = 1) : d72165 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82898, d72165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82898, d72165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70148 q = 1) (hb : d82899 q = 1) : d72166 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82899, d72166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82899, d72166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70148 q = 1) (hb : d82900 q = 1) : d72167 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82900, d72167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82900, d72167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70148 q = 1) (hb : d82901 q = 1) : d72168 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82901, d72168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82901, d72168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9754 (p : Pattern) (ha : d70148 p = 1) (hb : d82907 p = 1) : d72174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70148 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70148 q = 1) (hb : d82902 q = 1) : d72169 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82902, d72169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9753 q ha hb
    | true =>
      simp only [d82902, d72169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70148 q = 1) (hb : d82903 q = 1) : d72170 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82903, d72170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82903, d72170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70148 q = 1) (hb : d82904 q = 1) : d72171 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82904, d72171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82904, d72171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70148 q = 1) (hb : d82905 q = 1) : d72172 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82905, d72172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82905, d72172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70148 q = 1) (hb : d82906 q = 1) : d72173 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82906, d72173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82906, d72173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70148 q = 1) (hb : d82907 q = 1) : d72174 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82907, d72174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82907, d72174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9755 (p : Pattern) (ha : d59239 p = 1) (hb : d71479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51894 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h3 (q : Pattern) (ha : d59229 q = 1) (hb : d71468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59229, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59229, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59230 q = 1) (hb : d71469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59230, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59230, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59231 q = 1) (hb : d71470 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59231, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59231, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59232 q = 1) (hb : d71471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59232, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59232, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51901 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h9 (q : Pattern) (ha : d59235 q = 1) (hb : d71475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59235, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59235, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d59236 q = 1) (hb : d71476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59236, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59236, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d59237 q = 1) (hb : d71477 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59237, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59237, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d59238 q = 1) (hb : d71478 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59238, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59238, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d59239 q = 1) (hb : d71479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59239, d71479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59239, d71479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9756 (p : Pattern) (ha : d71472 p = 1) (hb : d83166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83165 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51894 q = 1) (hb : d71429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d59229 q = 1) (hb : d71468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59229, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59229, d71468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59230 q = 1) (hb : d71469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59230, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59230, d71469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d59231 q = 1) (hb : d71470 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59231, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59231, d71470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59232 q = 1) (hb : d71471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59232, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59232, d71471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71472 q = 1) (hb : d83166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71472, d83166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71472, d83166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro9757 (p : Pattern) (ha : d71964 p = 1) (hb : d83170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51901 q = 1) (hb : d71435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d59235 q = 1) (hb : d71475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59235, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59235, d71475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59236 q = 1) (hb : d71476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59236, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59236, d71476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59237 q = 1) (hb : d71477 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59237, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59237, d71477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59238 q = 1) (hb : d71478 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59238, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59238, d71478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71964 q = 1) (hb : d83170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71964, d83170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71964, d83170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro9758 (p : Pattern) (ha : d71974 p = 1) (hb : d83179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51935 q = 1) (hb : d71451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d71970 q = 1) (hb : d83175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71970, d83175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71970, d83175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d71971 q = 1) (hb : d83176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71971, d83176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71971, d83176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d71972 q = 1) (hb : d83177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71972, d83177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71972, d83177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71973 q = 1) (hb : d83178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71973, d83178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71973, d83178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71974 q = 1) (hb : d83179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71974, d83179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71974, d83179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9759 (p : Pattern) (ha : d71980 p = 1) (hb : d83184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71480 q = 1) (hb : d83167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71480, d83167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9756 q ha hb
    | true =>
      simp only [d71480, d83167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9755 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71481 q = 1) (hb : d83167 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71962 q = 1) (hb : d83168 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71962, d83168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71962, d83168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d71963 q = 1) (hb : d83169 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71963, d83169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71963, d83169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71965 q = 1) (hb : d83171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71965, d83171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71965, d83171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9757 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d83171 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71966 q = 1) (hb : d83171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71967 q = 1) (hb : d83172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71967, d83172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71967, d83172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d71968 q = 1) (hb : d83173 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71968, d83173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71968, d83173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d71969 q = 1) (hb : d83174 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71969, d83174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71969, d83174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71975 q = 1) (hb : d83180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71975, d83180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71975, d83180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9758 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d83180 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71976 q = 1) (hb : d83180 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d71976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d71977 q = 1) (hb : d83181 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71977, d83181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d71977, d83181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d71978 q = 1) (hb : d83182 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71978, d83182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d71978, d83182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d71979 q = 1) (hb : d83183 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71979, d83183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d71979, d83183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d71980 q = 1) (hb : d83184 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d71980, d83184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d71980, d83184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9760 (p : Pattern) (ha : d71986 p = 1) (hb : d83190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83161 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71981 q = 1) (hb : d83185 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d71981, d83185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71981, d83185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9759 q ha hb
  have h3 (q : Pattern) (ha : d71982 q = 1) (hb : d83186 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d71982, d83186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71982, d83186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71983 q = 1) (hb : d83187 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d71983, d83187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71983, d83187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d71984 q = 1) (hb : d83188 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d71984, d83188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71984, d83188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71985 q = 1) (hb : d83189 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d71985, d83189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71985, d83189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71986 q = 1) (hb : d83190 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d71986, d83190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71986, d83190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9761 (p : Pattern) (ha : d59298 p = 1) (hb : d71552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52238 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52238 q = 1) (hb : d71539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h3 (q : Pattern) (ha : d59288 q = 1) (hb : d71540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59288, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59288, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59289 q = 1) (hb : d71541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59289, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59289, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59290 q = 1) (hb : d71542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59290, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59290, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59291 q = 1) (hb : d71543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59291, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59291, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52248 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52248 q = 1) (hb : d71547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h9 (q : Pattern) (ha : d59294 q = 1) (hb : d71548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59294, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59294, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d59295 q = 1) (hb : d71549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59295, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59295, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d59296 q = 1) (hb : d71550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59296, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59296, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d59297 q = 1) (hb : d71551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59297, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59297, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d59298 q = 1) (hb : d71552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59298, d71552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59298, d71552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9762 (p : Pattern) (ha : d71544 p = 1) (hb : d83195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83194 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52238 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52238 q = 1) (hb : d71539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h4 (q : Pattern) (ha : d59288 q = 1) (hb : d71540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59288, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59288, d71540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59289 q = 1) (hb : d71541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59289, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59289, d71541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d59290 q = 1) (hb : d71542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59290, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59290, d71542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59291 q = 1) (hb : d71543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59291, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59291, d71543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71544 q = 1) (hb : d83195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71544, d83195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71544, d83195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro9763 (p : Pattern) (ha : d71989 p = 1) (hb : d83199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52248 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52248 q = 1) (hb : d71547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h3 (q : Pattern) (ha : d59294 q = 1) (hb : d71548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59294, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59294, d71548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59295 q = 1) (hb : d71549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59295, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59295, d71549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59296 q = 1) (hb : d71550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59296, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59296, d71550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59297 q = 1) (hb : d71551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59297, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59297, d71551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71989 q = 1) (hb : d83199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71989, d83199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71989, d83199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro9764 (p : Pattern) (ha : d72000 p = 1) (hb : d83208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52398 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52398 q = 1) (hb : d71995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d71996 q = 1) (hb : d83204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71996, d83204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71996, d83204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d71997 q = 1) (hb : d83205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71997, d83205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71997, d83205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d71998 q = 1) (hb : d83206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71998, d83206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71998, d83206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71999 q = 1) (hb : d83207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71999, d83207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71999, d83207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72000 q = 1) (hb : d83208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72000, d83208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72000, d83208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9765 (p : Pattern) (ha : d72006 p = 1) (hb : d83213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71553 q = 1) (hb : d83196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71553, d83196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9762 q ha hb
    | true =>
      simp only [d71553, d83196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9761 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83196 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71554 q = 1) (hb : d83196 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71987 q = 1) (hb : d83197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71987, d83197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71987, d83197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d71988 q = 1) (hb : d83198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71988, d83198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71988, d83198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71990 q = 1) (hb : d83200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71990, d83200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71990, d83200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9763 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d83200 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71991 q = 1) (hb : d83200 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71992 q = 1) (hb : d83201 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71992, d83201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71992, d83201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d71993 q = 1) (hb : d83202 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d71993, d83202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71993, d83202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d71994 q = 1) (hb : d83203 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d71994, d83203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71994, d83203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d72001 q = 1) (hb : d83209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72001, d83209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72001, d83209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9764 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d83209 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d72002 q = 1) (hb : d83209 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72003 q = 1) (hb : d83210 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72003, d83210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72003, d83210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d72004 q = 1) (hb : d83211 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72004, d83211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d72004, d83211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d72005 q = 1) (hb : d83212 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72005, d83212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d72005, d83212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d72006 q = 1) (hb : d83213 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72006, d83213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72006, d83213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9766 (p : Pattern) (ha : d72012 p = 1) (hb : d83219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72007 q = 1) (hb : d83214 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72007, d83214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72007, d83214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9765 q ha hb
  have h2 (q : Pattern) (ha : d72008 q = 1) (hb : d83215 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72008, d83215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72008, d83215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72009 q = 1) (hb : d83216 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72009, d83216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72009, d83216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72010 q = 1) (hb : d83217 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72010, d83217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72010, d83217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72011 q = 1) (hb : d83218 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72011, d83218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72011, d83218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72012 q = 1) (hb : d83219 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72012, d83219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72012, d83219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9767 (p : Pattern) (ha : d59358 p = 1) (hb : d71626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52460 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52460 q = 1) (hb : d71613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h3 (q : Pattern) (ha : d59348 q = 1) (hb : d71614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59348, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59348, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59349 q = 1) (hb : d71615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59349, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59349, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59350 q = 1) (hb : d71616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59350, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59350, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59351 q = 1) (hb : d71617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59351, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59351, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52470 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52470 q = 1) (hb : d71621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h9 (q : Pattern) (ha : d59354 q = 1) (hb : d71622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59354, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59354, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d59355 q = 1) (hb : d71623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59355, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59355, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d59356 q = 1) (hb : d71624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59356, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59356, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d59357 q = 1) (hb : d71625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59357, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59357, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d59358 q = 1) (hb : d71626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59358, d71626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59358, d71626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9768 (p : Pattern) (ha : d71618 p = 1) (hb : d83225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83224 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52460 q = 1) (hb : d71613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h4 (q : Pattern) (ha : d59348 q = 1) (hb : d71614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59348, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59348, d71614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59349 q = 1) (hb : d71615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59349, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59349, d71615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d59350 q = 1) (hb : d71616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59350, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59350, d71616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59351 q = 1) (hb : d71617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59351, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59351, d71617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71618 q = 1) (hb : d83225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71618, d83225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71618, d83225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro9769 (p : Pattern) (ha : d72016 p = 1) (hb : d83229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52470 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52470 q = 1) (hb : d71621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h3 (q : Pattern) (ha : d59354 q = 1) (hb : d71622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59354, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59354, d71622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59355 q = 1) (hb : d71623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59355, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59355, d71623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59356 q = 1) (hb : d71624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59356, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59356, d71624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59357 q = 1) (hb : d71625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59357, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59357, d71625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72016 q = 1) (hb : d83229 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72016, d83229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72016, d83229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro9770 (p : Pattern) (ha : d72027 p = 1) (hb : d83238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52635 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52635 q = 1) (hb : d72022 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d72022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d72023 q = 1) (hb : d83234 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72023, d83234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72023, d83234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d72024 q = 1) (hb : d83235 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d72024, d83235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72024, d83235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72025 q = 1) (hb : d83236 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d72025, d83236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72025, d83236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72026 q = 1) (hb : d83237 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d72026, d83237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72026, d83237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72027 q = 1) (hb : d83238 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72027, d83238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72027, d83238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9771 (p : Pattern) (ha : d72033 p = 1) (hb : d83243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71627 q = 1) (hb : d83226 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71627, d83226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9768 q ha hb
    | true =>
      simp only [d71627, d83226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9767 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83226 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71628 q = 1) (hb : d83226 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72014 q = 1) (hb : d83227 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72014, d83227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72014, d83227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72015 q = 1) (hb : d83228 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72015, d83228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72015, d83228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72017 q = 1) (hb : d83230 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72017, d83230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72017, d83230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9769 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d83230 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72018 q = 1) (hb : d83230 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72019 q = 1) (hb : d83231 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72019, d83231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72019, d83231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d72020 q = 1) (hb : d83232 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72020, d83232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d72020, d83232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d72021 q = 1) (hb : d83233 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72021, d83233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72021, d83233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d72028 q = 1) (hb : d83239 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72028, d83239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72028, d83239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9770 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d83239 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d72029 q = 1) (hb : d83239 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72030 q = 1) (hb : d83240 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72030, d83240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72030, d83240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d72031 q = 1) (hb : d83241 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72031, d83241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d72031, d83241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d72032 q = 1) (hb : d83242 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72032, d83242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d72032, d83242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d72033 q = 1) (hb : d83243 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72033, d83243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72033, d83243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9772 (p : Pattern) (ha : d72039 p = 1) (hb : d83249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72034 q = 1) (hb : d83244 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72034, d83244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72034, d83244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9771 q ha hb
  have h2 (q : Pattern) (ha : d72035 q = 1) (hb : d83245 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72035, d83245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72035, d83245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72036 q = 1) (hb : d83246 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72036, d83246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72036, d83246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72037 q = 1) (hb : d83247 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72037, d83247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72037, d83247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72038 q = 1) (hb : d83248 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72038, d83248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72038, d83248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72039 q = 1) (hb : d83249 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72039, d83249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72039, d83249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9773 (p : Pattern) (ha : d59419 p = 1) (hb : d71701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52743 q = 1) (hb : d71688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h3 (q : Pattern) (ha : d59409 q = 1) (hb : d71689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59409, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59409, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59410 q = 1) (hb : d71690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59410, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59410, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59411 q = 1) (hb : d71691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59411, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59411, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59412 q = 1) (hb : d71692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59412, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59412, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52753 q = 1) (hb : d71696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h9 (q : Pattern) (ha : d59415 q = 1) (hb : d71697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59415, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59415, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d59416 q = 1) (hb : d71698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59416, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59416, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d59417 q = 1) (hb : d71699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59417, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59417, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d59418 q = 1) (hb : d71700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59418, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59418, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d59419 q = 1) (hb : d71701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59419, d71701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59419, d71701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9774 (p : Pattern) (ha : d71693 p = 1) (hb : d83256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52743 q = 1) (hb : d71688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h4 (q : Pattern) (ha : d59409 q = 1) (hb : d71689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59409, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59409, d71689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59410 q = 1) (hb : d71690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59410, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59410, d71690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d59411 q = 1) (hb : d71691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59411, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59411, d71691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59412 q = 1) (hb : d71692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59412, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59412, d71692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71693 q = 1) (hb : d83256 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71693, d83256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71693, d83256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro9775 (p : Pattern) (ha : d72044 p = 1) (hb : d83260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52753 q = 1) (hb : d71696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h3 (q : Pattern) (ha : d59415 q = 1) (hb : d71697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59415, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59415, d71697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59416 q = 1) (hb : d71698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59416, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59416, d71698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59417 q = 1) (hb : d71699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59417, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59417, d71699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59418 q = 1) (hb : d71700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59418, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59418, d71700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72044 q = 1) (hb : d83260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72044, d83260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72044, d83260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro9776 (p : Pattern) (ha : d72055 p = 1) (hb : d83269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52929 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52929 q = 1) (hb : d72050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d72050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d72051 q = 1) (hb : d83265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72051, d83265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72051, d83265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d72052 q = 1) (hb : d83266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d72052, d83266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72052, d83266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72053 q = 1) (hb : d83267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d72053, d83267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72053, d83267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72054 q = 1) (hb : d83268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d72054, d83268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72054, d83268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72055 q = 1) (hb : d83269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72055, d83269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72055, d83269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9777 (p : Pattern) (ha : d72061 p = 1) (hb : d83274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71702 q = 1) (hb : d83257 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71702, d83257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9774 q ha hb
    | true =>
      simp only [d71702, d83257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9773 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83257 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71703 q = 1) (hb : d83257 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72042 q = 1) (hb : d83258 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72042, d83258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72042, d83258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72043 q = 1) (hb : d83259 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72043, d83259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72043, d83259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72045 q = 1) (hb : d83261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72045, d83261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72045, d83261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9775 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d83261 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72046 q = 1) (hb : d83261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72047 q = 1) (hb : d83262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72047, d83262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72047, d83262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d72048 q = 1) (hb : d83263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72048, d83263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d72048, d83263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d72049 q = 1) (hb : d83264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72049, d83264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72049, d83264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d72056 q = 1) (hb : d83270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72056, d83270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72056, d83270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9776 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d83270 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d72057 q = 1) (hb : d83270 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72058 q = 1) (hb : d83271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72058, d83271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72058, d83271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d72059 q = 1) (hb : d83272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72059, d83272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d72059, d83272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d72060 q = 1) (hb : d83273 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72060, d83273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d72060, d83273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d72061 q = 1) (hb : d83274 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72061, d83274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72061, d83274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9778 (p : Pattern) (ha : d72067 p = 1) (hb : d83280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72062 q = 1) (hb : d83275 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72062, d83275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72062, d83275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9777 q ha hb
  have h2 (q : Pattern) (ha : d72063 q = 1) (hb : d83276 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72063, d83276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72063, d83276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72064 q = 1) (hb : d83277 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72064, d83277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72064, d83277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72065 q = 1) (hb : d83278 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72065, d83278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72065, d83278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72066 q = 1) (hb : d83279 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72066, d83279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72066, d83279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72067 q = 1) (hb : d83280 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72067, d83280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72067, d83280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9779 (p : Pattern) (ha : d59481 p = 1) (hb : d71777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53064 q = 1) (hb : d71764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h3 (q : Pattern) (ha : d59471 q = 1) (hb : d71765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59471, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59471, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59472 q = 1) (hb : d71766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59472, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59472, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59473 q = 1) (hb : d71767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59473, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59473, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59474 q = 1) (hb : d71768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59474, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59474, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53074 q = 1) (hb : d71772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h9 (q : Pattern) (ha : d59477 q = 1) (hb : d71773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59477, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59477, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d59478 q = 1) (hb : d71774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59478, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59478, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d59479 q = 1) (hb : d71775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59479, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59479, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d59480 q = 1) (hb : d71776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59480, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59480, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d59481 q = 1) (hb : d71777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59481, d71777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59481, d71777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9780 (p : Pattern) (ha : d71769 p = 1) (hb : d83288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83287 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53064 q = 1) (hb : d71764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h4 (q : Pattern) (ha : d59471 q = 1) (hb : d71765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59471, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59471, d71765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59472 q = 1) (hb : d71766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59472, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59472, d71766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d59473 q = 1) (hb : d71767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59473, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59473, d71767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59474 q = 1) (hb : d71768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59474, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59474, d71768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71769 q = 1) (hb : d83288 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71769, d83288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71769, d83288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro9781 (p : Pattern) (ha : d72073 p = 1) (hb : d83292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53074 q = 1) (hb : d71772 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h3 (q : Pattern) (ha : d59477 q = 1) (hb : d71773 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59477, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59477, d71773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59478 q = 1) (hb : d71774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59478, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59478, d71774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59479 q = 1) (hb : d71775 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59479, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59479, d71775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59480 q = 1) (hb : d71776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59480, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59480, d71776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72073 q = 1) (hb : d83292 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72073, d83292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72073, d83292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro9782 (p : Pattern) (ha : d72084 p = 1) (hb : d83301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53244 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53244 q = 1) (hb : d72079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d72079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d72080 q = 1) (hb : d83297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72080, d83297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72080, d83297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d72081 q = 1) (hb : d83298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d72081, d83298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72081, d83298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72082 q = 1) (hb : d83299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d72082, d83299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72082, d83299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72083 q = 1) (hb : d83300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d72083, d83300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72083, d83300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72084 q = 1) (hb : d83301 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72084, d83301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72084, d83301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9783 (p : Pattern) (ha : d72090 p = 1) (hb : d83306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71778 q = 1) (hb : d83289 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71778, d83289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9780 q ha hb
    | true =>
      simp only [d71778, d83289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9779 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71779 q = 1) (hb : d83289 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72071 q = 1) (hb : d83290 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72071, d83290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72071, d83290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72072 q = 1) (hb : d83291 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72072, d83291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72072, d83291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72074 q = 1) (hb : d83293 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72074, d83293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72074, d83293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9781 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d83293 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72075 q = 1) (hb : d83293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72076 q = 1) (hb : d83294 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72076, d83294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72076, d83294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d72077 q = 1) (hb : d83295 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72077, d83295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d72077, d83295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d72078 q = 1) (hb : d83296 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72078, d83296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72078, d83296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d72085 q = 1) (hb : d83302 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72085, d83302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72085, d83302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9782 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d83302 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d72086 q = 1) (hb : d83302 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72087 q = 1) (hb : d83303 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72087, d83303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72087, d83303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d72088 q = 1) (hb : d83304 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72088, d83304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d72088, d83304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d72089 q = 1) (hb : d83305 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72089, d83305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d72089, d83305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d72090 q = 1) (hb : d83306 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72090, d83306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72090, d83306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9784 (p : Pattern) (ha : d72096 p = 1) (hb : d83312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72091 q = 1) (hb : d83307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72091, d83307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72091, d83307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9783 q ha hb
  have h2 (q : Pattern) (ha : d72092 q = 1) (hb : d83308 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72092, d83308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72092, d83308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72093 q = 1) (hb : d83309 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72093, d83309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72093, d83309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72094 q = 1) (hb : d83310 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72094, d83310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72094, d83310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72095 q = 1) (hb : d83311 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72095, d83311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72095, d83311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72096 q = 1) (hb : d83312 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72096, d83312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72096, d83312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9785 (p : Pattern) (ha : d59544 p = 1) (hb : d71854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53385 q = 1) (hb : d71841 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h3 (q : Pattern) (ha : d59534 q = 1) (hb : d71842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59534, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59534, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59535 q = 1) (hb : d71843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59535, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59535, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59536 q = 1) (hb : d71844 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59536, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59536, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59537 q = 1) (hb : d71845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59537, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59537, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53395 q = 1) (hb : d71849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h9 (q : Pattern) (ha : d59540 q = 1) (hb : d71850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59540, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59540, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d59541 q = 1) (hb : d71851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59541, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d59541, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d59542 q = 1) (hb : d71852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59542, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59542, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d59543 q = 1) (hb : d71853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59543, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59543, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d59544 q = 1) (hb : d71854 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59544, d71854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59544, d71854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9786 (p : Pattern) (ha : d71846 p = 1) (hb : d83321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83320 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53385 q = 1) (hb : d71841 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d71841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h4 (q : Pattern) (ha : d59534 q = 1) (hb : d71842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59534, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59534, d71842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59535 q = 1) (hb : d71843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59535, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59535, d71843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d59536 q = 1) (hb : d71844 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59536, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59536, d71844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59537 q = 1) (hb : d71845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59537, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d59537, d71845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d71846 q = 1) (hb : d83321 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71846, d83321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d71846, d83321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro9787 (p : Pattern) (ha : d72103 p = 1) (hb : d83325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53395 q = 1) (hb : d71849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d71849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h3 (q : Pattern) (ha : d59540 q = 1) (hb : d71850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59540, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59540, d71850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59541 q = 1) (hb : d71851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59541, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d59541, d71851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d59542 q = 1) (hb : d71852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59542, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59542, d71852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59543 q = 1) (hb : d71853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59543, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d59543, d71853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72103 q = 1) (hb : d83325 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72103, d83325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72103, d83325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro9788 (p : Pattern) (ha : d72114 p = 1) (hb : d83334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53561 q = 1) (hb : d72109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d72109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d72109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d72110 q = 1) (hb : d83330 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d72110, d83330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72110, d83330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d72111 q = 1) (hb : d83331 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d72111, d83331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72111, d83331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72112 q = 1) (hb : d83332 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d72112, d83332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72112, d83332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72113 q = 1) (hb : d83333 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d72113, d83333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72113, d83333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72114 q = 1) (hb : d83334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d72114, d83334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72114, d83334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9789 (p : Pattern) (ha : d72120 p = 1) (hb : d83339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71855 q = 1) (hb : d83322 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71855, d83322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9786 q ha hb
    | true =>
      simp only [d71855, d83322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9785 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71856 q = 1) (hb : d83322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72101 q = 1) (hb : d83323 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72101, d83323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72101, d83323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72102 q = 1) (hb : d83324 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72102, d83324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72102, d83324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72104 q = 1) (hb : d83326 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72104, d83326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72104, d83326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9787 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d83326 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d72105 q = 1) (hb : d83326 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72106 q = 1) (hb : d83327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72106, d83327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d72106, d83327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d72107 q = 1) (hb : d83328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72107, d83328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d72107, d83328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d72108 q = 1) (hb : d83329 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72108, d83329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72108, d83329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d72115 q = 1) (hb : d83335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d72115, d83335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72115, d83335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9788 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d83335 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d72116 q = 1) (hb : d83335 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d72116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72117 q = 1) (hb : d83336 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72117, d83336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d72117, d83336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d72118 q = 1) (hb : d83337 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72118, d83337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d72118, d83337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d72119 q = 1) (hb : d83338 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72119, d83338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d72119, d83338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d72120 q = 1) (hb : d83339 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72120, d83339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d72120, d83339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9790 (p : Pattern) (ha : d72126 p = 1) (hb : d83345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72121 q = 1) (hb : d83340 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72121, d83340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72121, d83340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9789 q ha hb
  have h2 (q : Pattern) (ha : d72122 q = 1) (hb : d83341 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72122, d83341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72122, d83341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d72123 q = 1) (hb : d83342 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72123, d83342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72123, d83342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72124 q = 1) (hb : d83343 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72124, d83343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72124, d83343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d72125 q = 1) (hb : d83344 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72125, d83344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72125, d83344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72126 q = 1) (hb : d83345 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72126, d83345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72126, d83345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9791 (p : Pattern) (ha : d72132 p = 1) (hb : d83351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d72013 q = 1) (hb : d83220 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72013, d83220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9760 q ha hb
    | true =>
      simp only [d72013, d83220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9766 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d72040 q = 1) (hb : d83250 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72040, d83250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72040, d83250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9772 q ha hb
  have h3 (q : Pattern) (ha : d72041 q = 1) (hb : d83251 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72041, d83251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d72041, d83251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72068 q = 1) (hb : d83281 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72068, d83281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72068, d83281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9778 q ha hb
  have h5 (q : Pattern) (ha : d72069 q = 1) (hb : d83282 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72069, d83282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72069, d83282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72070 q = 1) (hb : d83283 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72070, d83283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72070, d83283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d72097 q = 1) (hb : d83313 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72097, d83313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72097, d83313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9784 q ha hb
  have h8 (q : Pattern) (ha : d72098 q = 1) (hb : d83314 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72098, d83314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72098, d83314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d72099 q = 1) (hb : d83315 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72099, d83315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72099, d83315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d72100 q = 1) (hb : d83316 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72100, d83316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d72100, d83316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d72127 q = 1) (hb : d83346 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72127, d83346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72127, d83346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9790 q ha hb
  have h12 (q : Pattern) (ha : d72128 q = 1) (hb : d83347 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72128, d83347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72128, d83347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d72129 q = 1) (hb : d83348 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72129, d83348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72129, d83348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d72130 q = 1) (hb : d83349 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72130, d83349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72130, d83349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d72131 q = 1) (hb : d83350 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d72131, d83350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d72131, d83350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d72132 q = 1) (hb : d83351 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d72132, d83351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d72132, d83351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro9792 (p : Pattern) (ha : d72138 p = 1) (hb : d83357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72133 q = 1) (hb : d83352 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d72133, d83352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9791 q ha hb
    | true =>
      simp only [d72133, d83352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72134 q = 1) (hb : d83353 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d72134, d83353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72134, d83353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72135 q = 1) (hb : d83354 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d72135, d83354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72135, d83354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72136 q = 1) (hb : d83355 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d72136, d83355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72136, d83355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72137 q = 1) (hb : d83356 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d72137, d83356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72137, d83356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72138 q = 1) (hb : d83357 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d72138, d83357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72138, d83357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9793 (p : Pattern) (ha : d72144 p = 1) (hb : d83363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72139 q = 1) (hb : d83358 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d72139, d83358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9792 q ha hb
    | true =>
      simp only [d72139, d83358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72140 q = 1) (hb : d83359 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d72140, d83359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72140, d83359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72141 q = 1) (hb : d83360 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d72141, d83360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72141, d83360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72142 q = 1) (hb : d83361 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d72142, d83361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72142, d83361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72143 q = 1) (hb : d83362 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d72143, d83362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72143, d83362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72144 q = 1) (hb : d83363 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d72144, d83363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72144, d83363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9794 (p : Pattern) (ha : d72150 p = 1) (hb : d83369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72145 q = 1) (hb : d83364 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d72145, d83364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9793 q ha hb
    | true =>
      simp only [d72145, d83364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72146 q = 1) (hb : d83365 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d72146, d83365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72146, d83365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72147 q = 1) (hb : d83366 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d72147, d83366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72147, d83366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72148 q = 1) (hb : d83367 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d72148, d83367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72148, d83367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72149 q = 1) (hb : d83368 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d72149, d83368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72149, d83368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72150 q = 1) (hb : d83369 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d72150, d83369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72150, d83369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9795 (p : Pattern) (ha : d72156 p = 1) (hb : d83375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72151 q = 1) (hb : d83370 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d72151, d83370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9794 q ha hb
    | true =>
      simp only [d72151, d83370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72152 q = 1) (hb : d83371 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d72152, d83371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72152, d83371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72153 q = 1) (hb : d83372 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d72153, d83372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72153, d83372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72154 q = 1) (hb : d83373 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d72154, d83373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72154, d83373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72155 q = 1) (hb : d83374 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d72155, d83374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72155, d83374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72156 q = 1) (hb : d83375 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d72156, d83375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72156, d83375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9796 (p : Pattern) (ha : d72162 p = 1) (hb : d83381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72157 q = 1) (hb : d83376 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d72157, d83376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9795 q ha hb
    | true =>
      simp only [d72157, d83376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72158 q = 1) (hb : d83377 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d72158, d83377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72158, d83377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72159 q = 1) (hb : d83378 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d72159, d83378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72159, d83378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72160 q = 1) (hb : d83379 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d72160, d83379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72160, d83379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72161 q = 1) (hb : d83380 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d72161, d83380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72161, d83380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72162 q = 1) (hb : d83381 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d72162, d83381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72162, d83381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9797 (p : Pattern) (ha : d72168 p = 1) (hb : d83387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72163 q = 1) (hb : d83382 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d72163, d83382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9796 q ha hb
    | true =>
      simp only [d72163, d83382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72164 q = 1) (hb : d83383 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d72164, d83383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72164, d83383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72165 q = 1) (hb : d83384 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d72165, d83384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72165, d83384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72166 q = 1) (hb : d83385 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d72166, d83385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72166, d83385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72167 q = 1) (hb : d83386 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d72167, d83386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72167, d83386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72168 q = 1) (hb : d83387 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d72168, d83387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72168, d83387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9798 (p : Pattern) (ha : d72174 p = 1) (hb : d83393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72169 q = 1) (hb : d83388 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d72169, d83388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9797 q ha hb
    | true =>
      simp only [d72169, d83388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d72170 q = 1) (hb : d83389 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d72170, d83389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d72170, d83389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d72171 q = 1) (hb : d83390 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d72171, d83390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d72171, d83390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d72172 q = 1) (hb : d83391 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d72172, d83391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d72172, d83391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72173 q = 1) (hb : d83392 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d72173, d83392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d72173, d83392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72174 q = 1) (hb : d83393 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d72174, d83393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d72174, d83393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9799 (p : Pattern) (ha : d72174 p = 1) (hb : d83150 p = 1) : d72174 p = 1 := by
  have h0 (q : Pattern) (ha : d72174 q = 1) (hb : d83150 q = 1) : d72174 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9800 (p : Pattern) (ha : d4736 p = 1) (hb : d83662 p = 1) : d7347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d83662 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4735 q = 1) (hb : d83662 q = 1) : d7346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4735, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4736 q = 1) (hb : d83662 q = 1) : d7347 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d7347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d7347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9801 (p : Pattern) (ha : d76787 p = 1) (hb : d83662 p = 1) : d84548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d83662 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d83662 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5850 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
    | true =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76783 q = 1) (hb : d83662 q = 1) : d84544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76783, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76783, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d83662 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76784 q = 1) (hb : d83662 q = 1) : d84545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76784, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76784, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76785 q = 1) (hb : d83662 q = 1) : d84546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76785, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76785, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76786 q = 1) (hb : d83662 q = 1) : d84547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76786, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76786, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76787 q = 1) (hb : d83662 q = 1) : d84548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76787, d84548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76787, d84548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9802 (p : Pattern) (ha : d5355 p = 1) (hb : d83662 p = 1) : d7368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4733 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d83662 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4735 q = 1) (hb : d83662 q = 1) : d7346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4735, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5355 q = 1) (hb : d83662 q = 1) : d7368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d7368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5355, d7368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9803 (p : Pattern) (ha : d76792 p = 1) (hb : d83662 p = 1) : d84554 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d83662 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d83662 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5850 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
    | true =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76783 q = 1) (hb : d83662 q = 1) : d84544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76783, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76783, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d83662 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d76784 q = 1) (hb : d83662 q = 1) : d84545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76784, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76784, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76785 q = 1) (hb : d83662 q = 1) : d84546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76785, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76785, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76786 q = 1) (hb : d83662 q = 1) : d84547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76786, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76786, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d83662 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d83662 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d83662 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5856 q = 1) (hb : d83662 q = 1) : d84549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9802 q ha hb
    | true =>
      simp only [d5856, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76788 q = 1) (hb : d83662 q = 1) : d84550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76788, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76788, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d83662 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d76789 q = 1) (hb : d83662 q = 1) : d84551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76789, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76789, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76790 q = 1) (hb : d83662 q = 1) : d84552 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76790, d84552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76790, d84552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76791 q = 1) (hb : d83662 q = 1) : d84553 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76791, d84553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76791, d84553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d76792 q = 1) (hb : d83662 q = 1) : d84554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76792, d84554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76792, d84554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9804 (p : Pattern) (ha : d76799 p = 1) (hb : d83662 p = 1) : d84561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d83662 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5856 q = 1) (hb : d83662 q = 1) : d84549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9802 q ha hb
    | true =>
      simp only [d5856, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76788 q = 1) (hb : d83662 q = 1) : d84550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76788, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76788, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d83662 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76789 q = 1) (hb : d83662 q = 1) : d84551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76789, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76789, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76797 q = 1) (hb : d83662 q = 1) : d84559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76797, d84559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76797, d84559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76798 q = 1) (hb : d83662 q = 1) : d84560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76798, d84560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76798, d84560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76799 q = 1) (hb : d83662 q = 1) : d84561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76799, d84561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76799, d84561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9805 (p : Pattern) (ha : d5377 p = 1) (hb : d83662 p = 1) : d7411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d77842 q = 1) : d7275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8172 q ha hb
    | true =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d77842 q = 1) : d7276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5374 q = 1) (hb : d83662 q = 1) : d7408 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d83662, d7408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d83662, d7408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5375 q = 1) (hb : d83662 q = 1) : d7409 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d7409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5375, d7409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5376 q = 1) (hb : d83662 q = 1) : d7410 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d7410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5376, d7410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5377 q = 1) (hb : d83662 q = 1) : d7411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d7411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5377, d7411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9806 (p : Pattern) (ha : d76809 p = 1) (hb : d83662 p = 1) : d84572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d83662 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5874 q = 1) (hb : d83662 q = 1) : d84567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9805 q ha hb
    | true =>
      simp only [d5874, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76805 q = 1) (hb : d83662 q = 1) : d84568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76805, d84568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76805, d84568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d83662 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76806 q = 1) (hb : d83662 q = 1) : d84569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76806, d84569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76806, d84569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76807 q = 1) (hb : d83662 q = 1) : d84570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76807, d84570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76807, d84570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76808 q = 1) (hb : d83662 q = 1) : d84571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76808, d84571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76808, d84571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76809 q = 1) (hb : d83662 q = 1) : d84572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76809, d84572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76809, d84572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9807 (p : Pattern) (ha : d76815 p = 1) (hb : d83662 p = 1) : d84578 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d83662 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76793 q = 1) (hb : d83662 q = 1) : d84555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76793, d84555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9801 q ha hb
    | true =>
      simp only [d76793, d84555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9803 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d83662 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76794 q = 1) (hb : d83662 q = 1) : d84556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76794, d84556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76794, d84556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76795 q = 1) (hb : d83662 q = 1) : d84557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76795, d84557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76795, d84557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76796 q = 1) (hb : d83662 q = 1) : d84558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76796, d84558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76796, d84558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76800 q = 1) (hb : d83662 q = 1) : d84562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76800, d84562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76800, d84562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9804 q ha hb
  have h8 (q : Pattern) (ha : d76801 q = 1) (hb : d83662 q = 1) : d84563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76801, d84563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76801, d84563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d76802 q = 1) (hb : d83662 q = 1) : d84564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76802, d84564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76802, d84564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d76803 q = 1) (hb : d83662 q = 1) : d84565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76803, d84565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76803, d84565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d76804 q = 1) (hb : d83662 q = 1) : d84566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76804, d84566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76804, d84566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76810 q = 1) (hb : d83662 q = 1) : d84573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76810, d84573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76810, d84573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9806 q ha hb
  have h13 (q : Pattern) (ha : d76811 q = 1) (hb : d83662 q = 1) : d84574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76811, d84574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76811, d84574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d76812 q = 1) (hb : d83662 q = 1) : d84575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76812, d84575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76812, d84575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d76813 q = 1) (hb : d83662 q = 1) : d84576 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76813, d84576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76813, d84576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d76814 q = 1) (hb : d83662 q = 1) : d84577 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76814, d84577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76814, d84577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d76815 q = 1) (hb : d83662 q = 1) : d84578 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76815, d84578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76815, d84578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro9808 (p : Pattern) (ha : d5895 p = 1) (hb : d83662 p = 1) : d84588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5850 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
    | true =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d83662 q = 1) : d84584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d83662 q = 1) : d84585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d83662 q = 1) : d84586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d83662 q = 1) : d84587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5895 q = 1) (hb : d83662 q = 1) : d84588 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5895, d84588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5895, d84588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9809 (p : Pattern) (ha : d5902 p = 1) (hb : d83662 p = 1) : d84595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5850 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
    | true =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d83662 q = 1) : d84584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d83662 q = 1) : d84585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d83662 q = 1) : d84586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d83662 q = 1) : d84587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d83662 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5856 q = 1) (hb : d83662 q = 1) : d84549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9802 q ha hb
    | true =>
      simp only [d5856, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5898 q = 1) (hb : d83662 q = 1) : d84591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5898, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5899 q = 1) (hb : d83662 q = 1) : d84592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5899, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5900 q = 1) (hb : d83662 q = 1) : d84593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5901 q = 1) (hb : d83662 q = 1) : d84594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5902 q = 1) (hb : d83662 q = 1) : d84595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5902, d84595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5902, d84595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9810 (p : Pattern) (ha : d5952 p = 1) (hb : d83662 p = 1) : d84633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5850 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
    | true =>
      simp only [d5850, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5891 q = 1) (hb : d83662 q = 1) : d84584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5892 q = 1) (hb : d83662 q = 1) : d84585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5892, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5893 q = 1) (hb : d83662 q = 1) : d84586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5894 q = 1) (hb : d83662 q = 1) : d84587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d83662 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5952 q = 1) (hb : d83662 q = 1) : d84633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5952, d84633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5952, d84633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9811 (p : Pattern) (ha : d5907 p = 1) (hb : d83662 p = 1) : d84600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d83662 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5906 q = 1) (hb : d83662 q = 1) : d84599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5906, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5906, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5907 q = 1) (hb : d83662 q = 1) : d84600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5907, d84600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5907, d84600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9812 (p : Pattern) (ha : d5914 p = 1) (hb : d83662 p = 1) : d84607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5912 q = 1) (hb : d83662 q = 1) : d84605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5912, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5912, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5913 q = 1) (hb : d83662 q = 1) : d84606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5913, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5913, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5914 q = 1) (hb : d83662 q = 1) : d84607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5914, d84607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5914, d84607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9813 (p : Pattern) (ha : d330 p = 1) (hb : d77842 p = 1) : d7326 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d328 q = 1) : d328 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d329 q = 1) (hb : d77842 q = 1) : d7325 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d329, d77842, d7325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329, d77842, d7325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d330 q = 1) (hb : d77842 q = 1) : d7326 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d330, d7326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330, d7326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9814 (p : Pattern) (ha : d5921 p = 1) (hb : d83662 p = 1) : d7486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d331 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9813 q ha hb
    | true =>
      simp only [d331, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d332 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d332, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5918 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5918, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5918, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5919 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5919, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5919, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5920 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5920, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5920, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5921 q = 1) (hb : d83662 q = 1) : d7486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5921, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5921, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9815 (p : Pattern) (ha : d76825 p = 1) (hb : d83662 p = 1) : d84616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d83662 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5908 q = 1) (hb : d83662 q = 1) : d84601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9811 q ha hb
    | true =>
      simp only [d5908, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5909 q = 1) (hb : d83662 q = 1) : d84602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5910 q = 1) (hb : d83662 q = 1) : d84603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5910, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5911 q = 1) (hb : d83662 q = 1) : d84604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d83662 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5915 q = 1) (hb : d83662 q = 1) : d84608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9812 q ha hb
    | true =>
      simp only [d5915, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5916 q = 1) (hb : d83662 q = 1) : d84609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5917 q = 1) (hb : d83662 q = 1) : d84610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5917, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5922 q = 1) (hb : d83662 q = 1) : d84611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9814 q ha hb
    | true =>
      simp only [d5922, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
  have h11 (q : Pattern) (ha : d76821 q = 1) (hb : d83662 q = 1) : d84612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76821, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d83662 q = 1) : d7348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d7348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
    | true =>
      simp only [d4737, d7348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d83662 q = 1) : d7349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76822 q = 1) (hb : d83662 q = 1) : d84613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76822, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76823 q = 1) (hb : d83662 q = 1) : d84614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76823, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76824 q = 1) (hb : d83662 q = 1) : d84615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76824, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76825 q = 1) (hb : d83662 q = 1) : d84616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76825, d84616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76825, d84616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro9816 (p : Pattern) (ha : d5933 p = 1) (hb : d83662 p = 1) : d84617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4734 q = 1) (hb : d83662 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5906 q = 1) (hb : d83662 q = 1) : d84599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5906, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5906, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5933 q = 1) (hb : d83662 q = 1) : d84617 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5933, d84617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5933, d84617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9817 (p : Pattern) (ha : d5938 p = 1) (hb : d83662 p = 1) : d84622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4733 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4733, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5912 q = 1) (hb : d83662 q = 1) : d84605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5912, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5912, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5913 q = 1) (hb : d83662 q = 1) : d84606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5913, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5913, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5938 q = 1) (hb : d83662 q = 1) : d84622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5938, d84622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5938, d84622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9818 (p : Pattern) (ha : d5942 p = 1) (hb : d83662 p = 1) : d7507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9813 q ha hb
    | true =>
      simp only [d331, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5918 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5918, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5918, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5919 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5919, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5919, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5920 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5920, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5920, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5942 q = 1) (hb : d83662 q = 1) : d7507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5942, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5942, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9819 (p : Pattern) (ha : d76830 p = 1) (hb : d83662 p = 1) : d84631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d83662 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5908 q = 1) (hb : d83662 q = 1) : d84601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9811 q ha hb
    | true =>
      simp only [d5908, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5909 q = 1) (hb : d83662 q = 1) : d84602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5910 q = 1) (hb : d83662 q = 1) : d84603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5910, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5911 q = 1) (hb : d83662 q = 1) : d84604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d83662 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5915 q = 1) (hb : d83662 q = 1) : d84608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9812 q ha hb
    | true =>
      simp only [d5915, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5916 q = 1) (hb : d83662 q = 1) : d84609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5917 q = 1) (hb : d83662 q = 1) : d84610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5917, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5922 q = 1) (hb : d83662 q = 1) : d84611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9814 q ha hb
    | true =>
      simp only [d5922, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
  have h11 (q : Pattern) (ha : d76821 q = 1) (hb : d83662 q = 1) : d84612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76821, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76821, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d83662 q = 1) : d7348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d7348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9800 q ha hb
    | true =>
      simp only [d4737, d7348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d83662 q = 1) : d7349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76822 q = 1) (hb : d83662 q = 1) : d84613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76822, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76822, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76823 q = 1) (hb : d83662 q = 1) : d84614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76823, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76823, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76824 q = 1) (hb : d83662 q = 1) : d84615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76824, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76824, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d83662 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d5934 q = 1) (hb : d83662 q = 1) : d84618 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5934, d84618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9816 q ha hb
    | true =>
      simp only [d5934, d84618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5935 q = 1) (hb : d83662 q = 1) : d84619 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5935, d84619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5935, d84619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5936 q = 1) (hb : d83662 q = 1) : d84620 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5936, d84620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5936, d84620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d5937 q = 1) (hb : d83662 q = 1) : d84621 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5937, d84621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5937, d84621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d83662 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d5939 q = 1) (hb : d83662 q = 1) : d84623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5939, d84623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9817 q ha hb
    | true =>
      simp only [d5939, d84623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d5940 q = 1) (hb : d83662 q = 1) : d84624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5940, d84624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5940, d84624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d5941 q = 1) (hb : d83662 q = 1) : d84625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5941, d84625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5941, d84625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d5943 q = 1) (hb : d83662 q = 1) : d84626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9818 q ha hb
    | true =>
      simp only [d5943, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9802 q ha hb
  have h27 (q : Pattern) (ha : d76826 q = 1) (hb : d83662 q = 1) : d84627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76826, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d83662 q = 1) : d7369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d7369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9802 q ha hb
    | true =>
      simp only [d5356, d7369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d83662 q = 1) : d7370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76827 q = 1) (hb : d83662 q = 1) : d84628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76827, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76828 q = 1) (hb : d83662 q = 1) : d84629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76828, d84629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76828, d84629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76829 q = 1) (hb : d83662 q = 1) : d84630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76829, d84630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76829, d84630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76830 q = 1) (hb : d83662 q = 1) : d84631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76830, d84631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76830, d84631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro9820 (p : Pattern) (ha : d76837 p = 1) (hb : d83662 p = 1) : d84640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5943 q = 1) (hb : d83662 q = 1) : d84626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9818 q ha hb
    | true =>
      simp only [d5943, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9802 q ha hb
  have h2 (q : Pattern) (ha : d76826 q = 1) (hb : d83662 q = 1) : d84627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76826, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76826, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d83662 q = 1) : d7369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d7369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9802 q ha hb
    | true =>
      simp only [d5356, d7369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d83662 q = 1) : d7370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76827 q = 1) (hb : d83662 q = 1) : d84628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76827, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76827, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76835 q = 1) (hb : d83662 q = 1) : d84638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76835, d84638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76835, d84638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76836 q = 1) (hb : d83662 q = 1) : d84639 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76836, d84639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76836, d84639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76837 q = 1) (hb : d83662 q = 1) : d84640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76837, d84640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76837, d84640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9821 (p : Pattern) (ha : d423 p = 1) (hb : d77842 p = 1) : d7390 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d421 q = 1) : d421 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d235 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d422 q = 1) (hb : d77842 q = 1) : d7389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d422, d77842, d7389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d422, d77842, d7389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d423 q = 1) (hb : d77842 q = 1) : d7390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d423, d7390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d423, d7390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9822 (p : Pattern) (ha : d5968 p = 1) (hb : d83662 p = 1) : d7554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d424 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9821 q ha hb
    | true =>
      simp only [d424, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d425 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d425, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d425, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5965 q = 1) (hb : d83662 q = 1) : d7551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5965, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5965, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5966 q = 1) (hb : d83662 q = 1) : d7552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5966, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5966, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5967 q = 1) (hb : d83662 q = 1) : d7553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5967, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5967, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5968 q = 1) (hb : d83662 q = 1) : d7554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5968, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5968, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9823 (p : Pattern) (ha : d76847 p = 1) (hb : d83662 p = 1) : d84651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5969 q = 1) (hb : d83662 q = 1) : d84646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5969, d84646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9822 q ha hb
    | true =>
      simp only [d5969, d84646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9805 q ha hb
  have h2 (q : Pattern) (ha : d76843 q = 1) (hb : d83662 q = 1) : d84647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76843, d84647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76843, d84647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d83662 q = 1) : d7412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d7412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9805 q ha hb
    | true =>
      simp only [d5378, d7412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d83662 q = 1) : d7413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d7413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d7413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76844 q = 1) (hb : d83662 q = 1) : d84648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76844, d84648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76844, d84648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76845 q = 1) (hb : d83662 q = 1) : d84649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76845, d84649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76845, d84649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76846 q = 1) (hb : d83662 q = 1) : d84650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76846, d84650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76846, d84650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76847 q = 1) (hb : d83662 q = 1) : d84651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76847, d84651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76847, d84651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9824 (p : Pattern) (ha : d76853 p = 1) (hb : d83662 p = 1) : d84657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5896 q = 1) (hb : d83662 q = 1) : d84589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5896, d84589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5896, d84589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9808 q ha hb
  have h2 (q : Pattern) (ha : d5897 q = 1) (hb : d83662 q = 1) : d84590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5897, d84590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5897, d84590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5903 q = 1) (hb : d83662 q = 1) : d84596 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9808 q ha hb
    | true =>
      simp only [d5903, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9809 q ha hb
  have h4 (q : Pattern) (ha : d5904 q = 1) (hb : d83662 q = 1) : d84597 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5904, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5905 q = 1) (hb : d83662 q = 1) : d84598 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5905, d84598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5905, d84598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76831 q = 1) (hb : d83662 q = 1) : d84632 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76831, d84632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9815 q ha hb
    | true =>
      simp only [d76831, d84632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9819 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d83662 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5953 q = 1) (hb : d83662 q = 1) : d84634 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5953, d84634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9810 q ha hb
    | true =>
      simp only [d5953, d84634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76832 q = 1) (hb : d83662 q = 1) : d84635 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76832, d84635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76832, d84635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76833 q = 1) (hb : d83662 q = 1) : d84636 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76833, d84636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76833, d84636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76834 q = 1) (hb : d83662 q = 1) : d84637 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76834, d84637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76834, d84637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76838 q = 1) (hb : d83662 q = 1) : d84641 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76838, d84641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76838, d84641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9820 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d83662 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d76839 q = 1) (hb : d83662 q = 1) : d84642 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76839, d84642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76839, d84642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76840 q = 1) (hb : d83662 q = 1) : d84643 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76840, d84643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76840, d84643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76841 q = 1) (hb : d83662 q = 1) : d84644 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76841, d84644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76841, d84644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d76842 q = 1) (hb : d83662 q = 1) : d84645 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76842, d84645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76842, d84645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76848 q = 1) (hb : d83662 q = 1) : d84652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76848, d84652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76848, d84652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9823 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d83662 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d76849 q = 1) (hb : d83662 q = 1) : d84653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76849, d84653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76849, d84653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d76850 q = 1) (hb : d83662 q = 1) : d84654 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76850, d84654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76850, d84654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76851 q = 1) (hb : d83662 q = 1) : d84655 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76851, d84655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76851, d84655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76852 q = 1) (hb : d83662 q = 1) : d84656 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76852, d84656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76852, d84656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d76853 q = 1) (hb : d83662 q = 1) : d84657 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76853, d84657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76853, d84657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro9825 (p : Pattern) (ha : d76859 p = 1) (hb : d83662 p = 1) : d84663 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d83662 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76816 q = 1) (hb : d83662 q = 1) : d84579 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76816, d84579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76816, d84579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9807 q ha hb
  have h3 (q : Pattern) (ha : d76817 q = 1) (hb : d83662 q = 1) : d84580 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76817, d84580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76817, d84580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76818 q = 1) (hb : d83662 q = 1) : d84581 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76818, d84581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76818, d84581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76819 q = 1) (hb : d83662 q = 1) : d84582 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76819, d84582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76819, d84582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76820 q = 1) (hb : d83662 q = 1) : d84583 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76820, d84583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76820, d84583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76854 q = 1) (hb : d83662 q = 1) : d84658 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76854, d84658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76854, d84658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9824 q ha hb
  have h8 (q : Pattern) (ha : d76855 q = 1) (hb : d83662 q = 1) : d84659 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76855, d84659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76855, d84659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76856 q = 1) (hb : d83662 q = 1) : d84660 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76856, d84660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76856, d84660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76857 q = 1) (hb : d83662 q = 1) : d84661 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76857, d84661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76857, d84661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76858 q = 1) (hb : d83662 q = 1) : d84662 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76858, d84662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76858, d84662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76859 q = 1) (hb : d83662 q = 1) : d84663 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76859, d84663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76859, d84663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9826 (p : Pattern) (ha : d5399 p = 1) (hb : d83662 p = 1) : d7486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5398 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5399 q = 1) (hb : d83662 q = 1) : d7486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5399, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5399, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9827 (p : Pattern) (ha : d5997 p = 1) (hb : d83662 p = 1) : d84669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d83662 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5992 q = 1) (hb : d83662 q = 1) : d84664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9826 q ha hb
    | true =>
      simp only [d5992, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5993 q = 1) (hb : d83662 q = 1) : d84665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5994 q = 1) (hb : d83662 q = 1) : d84666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5994, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5995 q = 1) (hb : d83662 q = 1) : d84667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5996 q = 1) (hb : d83662 q = 1) : d84668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5997 q = 1) (hb : d83662 q = 1) : d84669 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5997, d84669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5997, d84669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9828 (p : Pattern) (ha : d5406 p = 1) (hb : d83662 p = 1) : d7507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5396 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5398 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5406 q = 1) (hb : d83662 q = 1) : d7507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5406, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5406, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9829 (p : Pattern) (ha : d6005 p = 1) (hb : d83662 p = 1) : d84677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d83662 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5992 q = 1) (hb : d83662 q = 1) : d84664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9826 q ha hb
    | true =>
      simp only [d5992, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5993 q = 1) (hb : d83662 q = 1) : d84665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5994 q = 1) (hb : d83662 q = 1) : d84666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5994, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5995 q = 1) (hb : d83662 q = 1) : d84667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5996 q = 1) (hb : d83662 q = 1) : d84668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d83662 q = 1) : d501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6000 q = 1) (hb : d83662 q = 1) : d84672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9828 q ha hb
    | true =>
      simp only [d6000, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6001 q = 1) (hb : d83662 q = 1) : d84673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6001, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6002 q = 1) (hb : d83662 q = 1) : d84674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6002, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6003 q = 1) (hb : d83662 q = 1) : d84675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6004 q = 1) (hb : d83662 q = 1) : d84676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6005 q = 1) (hb : d83662 q = 1) : d84677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6005, d84677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6005, d84677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9830 (p : Pattern) (ha : d4824 p = 1) (hb : d77842 p = 1) : d7326 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d328 q = 1) : d328 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4823 q = 1) (hb : d77842 q = 1) : d7325 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d4823, d77842, d7325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4823, d77842, d7325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4824 q = 1) (hb : d77842 q = 1) : d7326 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d4824, d7326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4824, d7326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9831 (p : Pattern) (ha : d4830 p = 1) (hb : d83662 p = 1) : d7486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4825 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9830 q ha hb
    | true =>
      simp only [d4825, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4826 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4826, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4827 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4827, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4828 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4828, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4829 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4829, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4830 q = 1) (hb : d83662 q = 1) : d7486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4830, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4830, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9832 (p : Pattern) (ha : d6061 p = 1) (hb : d83662 p = 1) : d84720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d83662 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6056 q = 1) (hb : d83662 q = 1) : d84664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6056, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9831 q ha hb
    | true =>
      simp only [d6056, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6057 q = 1) (hb : d83662 q = 1) : d84665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6057, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6057, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6058 q = 1) (hb : d83662 q = 1) : d84666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6058, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6058, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6059 q = 1) (hb : d83662 q = 1) : d84667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6059, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6059, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6060 q = 1) (hb : d83662 q = 1) : d84668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6060, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6060, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d83662 q = 1) : d637 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6061 q = 1) (hb : d83662 q = 1) : d84720 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6061, d84720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6061, d84720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9833 (p : Pattern) (ha : d6010 p = 1) (hb : d83662 p = 1) : d84682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6009 q = 1) (hb : d83662 q = 1) : d84681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6009, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6009, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6010 q = 1) (hb : d83662 q = 1) : d84682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6010, d84682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6010, d84682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9834 (p : Pattern) (ha : d6017 p = 1) (hb : d83662 p = 1) : d84689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6015 q = 1) (hb : d83662 q = 1) : d84687 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6015, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6015, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6016 q = 1) (hb : d83662 q = 1) : d84688 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6016, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6016, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6017 q = 1) (hb : d83662 q = 1) : d84689 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6017, d84689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6017, d84689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9835 (p : Pattern) (ha : d554 p = 1) (hb : d77842 p = 1) : d7465 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d552 q = 1) : d552 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d553 q = 1) (hb : d77842 q = 1) : d7464 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d553, d77842, d7464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d553, d77842, d7464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d554 q = 1) (hb : d77842 q = 1) : d7465 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d554, d7465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d554, d7465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9836 (p : Pattern) (ha : d6024 p = 1) (hb : d83662 p = 1) : d84696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d555 q = 1) (hb : d77842 q = 1) : d7466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9835 q ha hb
    | true =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d556 q = 1) (hb : d77842 q = 1) : d7467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6021 q = 1) (hb : d83662 q = 1) : d84693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6021, d83662, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6021, d83662, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6022 q = 1) (hb : d83662 q = 1) : d84694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6022, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6022, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6023 q = 1) (hb : d83662 q = 1) : d84695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6023, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6023, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6024 q = 1) (hb : d83662 q = 1) : d84696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6024, d84696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6024, d84696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9837 (p : Pattern) (ha : d76864 p = 1) (hb : d83662 p = 1) : d84702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d83662 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6011 q = 1) (hb : d83662 q = 1) : d84683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9833 q ha hb
    | true =>
      simp only [d6011, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6012 q = 1) (hb : d83662 q = 1) : d84684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6013 q = 1) (hb : d83662 q = 1) : d84685 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6013, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6014 q = 1) (hb : d83662 q = 1) : d84686 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d83662 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6018 q = 1) (hb : d83662 q = 1) : d84690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9834 q ha hb
    | true =>
      simp only [d6018, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6019 q = 1) (hb : d83662 q = 1) : d84691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6020 q = 1) (hb : d83662 q = 1) : d84692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6020, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6025 q = 1) (hb : d83662 q = 1) : d84697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9836 q ha hb
    | true =>
      simp only [d6025, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9831 q ha hb
  have h11 (q : Pattern) (ha : d76860 q = 1) (hb : d83662 q = 1) : d84698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76860, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5400 q = 1) (hb : d83662 q = 1) : d7487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9826 q ha hb
    | true =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5401 q = 1) (hb : d83662 q = 1) : d7488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76861 q = 1) (hb : d83662 q = 1) : d84699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76861, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76862 q = 1) (hb : d83662 q = 1) : d84700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76862, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76863 q = 1) (hb : d83662 q = 1) : d84701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76863, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76864 q = 1) (hb : d83662 q = 1) : d84702 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76864, d84702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76864, d84702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro9838 (p : Pattern) (ha : d6036 p = 1) (hb : d83662 p = 1) : d84703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6009 q = 1) (hb : d83662 q = 1) : d84681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6009, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6009, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6036 q = 1) (hb : d83662 q = 1) : d84703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6036, d84703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6036, d84703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9839 (p : Pattern) (ha : d6041 p = 1) (hb : d83662 p = 1) : d84708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5396 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5396, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6015 q = 1) (hb : d83662 q = 1) : d84687 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6015, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6015, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6016 q = 1) (hb : d83662 q = 1) : d84688 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6016, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6016, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6041 q = 1) (hb : d83662 q = 1) : d84708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6041, d84708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6041, d84708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9840 (p : Pattern) (ha : d6045 p = 1) (hb : d83662 p = 1) : d84712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d77842 q = 1) : d7466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9835 q ha hb
    | true =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d77842 q = 1) : d7467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6021 q = 1) (hb : d83662 q = 1) : d84693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6021, d83662, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6021, d83662, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6022 q = 1) (hb : d83662 q = 1) : d84694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6022, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6022, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6023 q = 1) (hb : d83662 q = 1) : d84695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6023, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6023, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6045 q = 1) (hb : d83662 q = 1) : d84712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6045, d84712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6045, d84712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9841 (p : Pattern) (ha : d6046 p = 1) (hb : d83662 p = 1) : d7507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4825 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9830 q ha hb
    | true =>
      simp only [d4825, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4826 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4826, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4827 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4827, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4828 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4828, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4829 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4829, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6046 q = 1) (hb : d83662 q = 1) : d7507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6046, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6046, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9842 (p : Pattern) (ha : d76869 p = 1) (hb : d83662 p = 1) : d84718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d83662 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6011 q = 1) (hb : d83662 q = 1) : d84683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9833 q ha hb
    | true =>
      simp only [d6011, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6012 q = 1) (hb : d83662 q = 1) : d84684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6013 q = 1) (hb : d83662 q = 1) : d84685 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6013, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6014 q = 1) (hb : d83662 q = 1) : d84686 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d83662 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6018 q = 1) (hb : d83662 q = 1) : d84690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9834 q ha hb
    | true =>
      simp only [d6018, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6019 q = 1) (hb : d83662 q = 1) : d84691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6020 q = 1) (hb : d83662 q = 1) : d84692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6020, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6025 q = 1) (hb : d83662 q = 1) : d84697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9836 q ha hb
    | true =>
      simp only [d6025, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9831 q ha hb
  have h11 (q : Pattern) (ha : d76860 q = 1) (hb : d83662 q = 1) : d84698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76860, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76860, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5400 q = 1) (hb : d83662 q = 1) : d7487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9826 q ha hb
    | true =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5401 q = 1) (hb : d83662 q = 1) : d7488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76861 q = 1) (hb : d83662 q = 1) : d84699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76861, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76861, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76862 q = 1) (hb : d83662 q = 1) : d84700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76862, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76862, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76863 q = 1) (hb : d83662 q = 1) : d84701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76863, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76863, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d610 q = 1) (hb : d83662 q = 1) : d610 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6037 q = 1) (hb : d83662 q = 1) : d84704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6037, d84704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9838 q ha hb
    | true =>
      simp only [d6037, d84704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6038 q = 1) (hb : d83662 q = 1) : d84705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6038, d84705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6038, d84705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6039 q = 1) (hb : d83662 q = 1) : d84706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6039, d84706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6039, d84706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6040 q = 1) (hb : d83662 q = 1) : d84707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6040, d84707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6040, d84707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d616 q = 1) (hb : d83662 q = 1) : d616 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6042 q = 1) (hb : d83662 q = 1) : d84709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6042, d84709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9839 q ha hb
    | true =>
      simp only [d6042, d84709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6043 q = 1) (hb : d83662 q = 1) : d84710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6043, d84710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6043, d84710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6044 q = 1) (hb : d83662 q = 1) : d84711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6044, d84711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6044, d84711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6047 q = 1) (hb : d83662 q = 1) : d84713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9840 q ha hb
    | true =>
      simp only [d6047, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9841 q ha hb
  have h27 (q : Pattern) (ha : d76865 q = 1) (hb : d83662 q = 1) : d84714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76865, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5407 q = 1) (hb : d83662 q = 1) : d7508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9828 q ha hb
    | true =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5408 q = 1) (hb : d83662 q = 1) : d7509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76866 q = 1) (hb : d83662 q = 1) : d84715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76866, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76867 q = 1) (hb : d83662 q = 1) : d84716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76867, d84716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76867, d84716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76868 q = 1) (hb : d83662 q = 1) : d84717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76868, d84717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76868, d84717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76869 q = 1) (hb : d83662 q = 1) : d84718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76869, d84718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76869, d84718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro9843 (p : Pattern) (ha : d76876 p = 1) (hb : d83662 p = 1) : d84727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6047 q = 1) (hb : d83662 q = 1) : d84713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9840 q ha hb
    | true =>
      simp only [d6047, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9841 q ha hb
  have h2 (q : Pattern) (ha : d76865 q = 1) (hb : d83662 q = 1) : d84714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76865, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76865, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d83662 q = 1) : d7508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9828 q ha hb
    | true =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5408 q = 1) (hb : d83662 q = 1) : d7509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76866 q = 1) (hb : d83662 q = 1) : d84715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76866, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76866, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76874 q = 1) (hb : d83662 q = 1) : d84725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76874, d84725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76874, d84725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76875 q = 1) (hb : d83662 q = 1) : d84726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76875, d84726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76875, d84726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76876 q = 1) (hb : d83662 q = 1) : d84727 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76876, d84727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76876, d84727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9844 (p : Pattern) (ha : d5428 p = 1) (hb : d83662 p = 1) : d7554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8199 q ha hb
    | true =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5425 q = 1) (hb : d83662 q = 1) : d7551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5426 q = 1) (hb : d83662 q = 1) : d7552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5426, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5427 q = 1) (hb : d83662 q = 1) : d7553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5427, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5428 q = 1) (hb : d83662 q = 1) : d7554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5428, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9845 (p : Pattern) (ha : d670 p = 1) (hb : d77842 p = 1) : d7529 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d668 q = 1) : d668 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d669 q = 1) (hb : d77842 q = 1) : d7528 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d669, d77842, d7528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d669, d77842, d7528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d670 q = 1) (hb : d77842 q = 1) : d7529 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d670, d7529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d670, d7529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9846 (p : Pattern) (ha : d6077 p = 1) (hb : d83662 p = 1) : d84736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d671 q = 1) (hb : d77842 q = 1) : d7530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d7530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9845 q ha hb
    | true =>
      simp only [d671, d7530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d672 q = 1) (hb : d77842 q = 1) : d7531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d672, d7531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d672, d7531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6074 q = 1) (hb : d83662 q = 1) : d84733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6074, d83662, d84733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6074, d83662, d84733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6075 q = 1) (hb : d83662 q = 1) : d84734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6075, d84734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6075, d84734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6076 q = 1) (hb : d83662 q = 1) : d84735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6076, d84735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6076, d84735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6077 q = 1) (hb : d83662 q = 1) : d84736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6077, d84736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6077, d84736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9847 (p : Pattern) (ha : d6084 p = 1) (hb : d77842 p = 1) : d7390 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d421 q = 1) : d421 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6083 q = 1) (hb : d77842 q = 1) : d7389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6083, d77842, d7389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6083, d77842, d7389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6084 q = 1) (hb : d77842 q = 1) : d7390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6084, d7390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6084, d7390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9848 (p : Pattern) (ha : d6090 p = 1) (hb : d83662 p = 1) : d7554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6085 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6085, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9847 q ha hb
    | true =>
      simp only [d6085, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6086 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6086, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6086, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6087 q = 1) (hb : d83662 q = 1) : d7551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6087, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6087, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6088 q = 1) (hb : d83662 q = 1) : d7552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6088, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6088, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6089 q = 1) (hb : d83662 q = 1) : d7553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6089, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6089, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6090 q = 1) (hb : d83662 q = 1) : d7554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6090, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6090, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9849 (p : Pattern) (ha : d76886 p = 1) (hb : d83662 p = 1) : d84742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6091 q = 1) (hb : d83662 q = 1) : d84737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6091, d84737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9846 q ha hb
    | true =>
      simp only [d6091, d84737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9848 q ha hb
  have h2 (q : Pattern) (ha : d76882 q = 1) (hb : d83662 q = 1) : d84738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76882, d84738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76882, d84738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d83662 q = 1) : d7555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d7555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9844 q ha hb
    | true =>
      simp only [d5429, d7555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5430 q = 1) (hb : d83662 q = 1) : d7556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d7556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5430, d7556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76883 q = 1) (hb : d83662 q = 1) : d84739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76883, d84739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76883, d84739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76884 q = 1) (hb : d83662 q = 1) : d84740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76884, d84740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76884, d84740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76885 q = 1) (hb : d83662 q = 1) : d84741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76885, d84741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76885, d84741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76886 q = 1) (hb : d83662 q = 1) : d84742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76886, d84742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76886, d84742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9850 (p : Pattern) (ha : d76892 p = 1) (hb : d83662 p = 1) : d84748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5998 q = 1) (hb : d83662 q = 1) : d84670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5998, d84670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5998, d84670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9827 q ha hb
  have h2 (q : Pattern) (ha : d5999 q = 1) (hb : d83662 q = 1) : d84671 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5999, d84671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5999, d84671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6006 q = 1) (hb : d83662 q = 1) : d84678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d84678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9827 q ha hb
    | true =>
      simp only [d6006, d84678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9829 q ha hb
  have h4 (q : Pattern) (ha : d6007 q = 1) (hb : d83662 q = 1) : d84679 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d84679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6007, d84679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6008 q = 1) (hb : d83662 q = 1) : d84680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6008, d84680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6008, d84680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76870 q = 1) (hb : d83662 q = 1) : d84719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76870, d84719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9837 q ha hb
    | true =>
      simp only [d76870, d84719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9842 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d83662 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6062 q = 1) (hb : d83662 q = 1) : d84721 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6062, d84721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9832 q ha hb
    | true =>
      simp only [d6062, d84721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76871 q = 1) (hb : d83662 q = 1) : d84722 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76871, d84722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76871, d84722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76872 q = 1) (hb : d83662 q = 1) : d84723 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76872, d84723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76872, d84723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76873 q = 1) (hb : d83662 q = 1) : d84724 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76873, d84724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76873, d84724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76877 q = 1) (hb : d83662 q = 1) : d84728 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76877, d84728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76877, d84728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9843 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d83662 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d76878 q = 1) (hb : d83662 q = 1) : d84729 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76878, d84729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76878, d84729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76879 q = 1) (hb : d83662 q = 1) : d84730 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76879, d84730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76879, d84730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76880 q = 1) (hb : d83662 q = 1) : d84731 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76880, d84731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76880, d84731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d76881 q = 1) (hb : d83662 q = 1) : d84732 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76881, d84732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76881, d84732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76887 q = 1) (hb : d83662 q = 1) : d84743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76887, d84743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76887, d84743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9849 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d83662 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d76888 q = 1) (hb : d83662 q = 1) : d84744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76888, d84744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76888, d84744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d76889 q = 1) (hb : d83662 q = 1) : d84745 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76889, d84745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76889, d84745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76890 q = 1) (hb : d83662 q = 1) : d84746 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76890, d84746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76890, d84746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76891 q = 1) (hb : d83662 q = 1) : d84747 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76891, d84747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76891, d84747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d76892 q = 1) (hb : d83662 q = 1) : d84748 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76892, d84748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76892, d84748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro9851 (p : Pattern) (ha : d76898 p = 1) (hb : d83662 p = 1) : d84754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76893 q = 1) (hb : d83662 q = 1) : d84749 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76893, d84749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76893, d84749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9850 q ha hb
  have h2 (q : Pattern) (ha : d76894 q = 1) (hb : d83662 q = 1) : d84750 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76894, d84750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76894, d84750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76895 q = 1) (hb : d83662 q = 1) : d84751 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76895, d84751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76895, d84751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76896 q = 1) (hb : d83662 q = 1) : d84752 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76896, d84752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76896, d84752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76897 q = 1) (hb : d83662 q = 1) : d84753 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76897, d84753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76897, d84753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76898 q = 1) (hb : d83662 q = 1) : d84754 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76898, d84754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76898, d84754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9852 (p : Pattern) (ha : d6118 p = 1) (hb : d83662 p = 1) : d7634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6117 q = 1) (hb : d83662 q = 1) : d7633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6117, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6118 q = 1) (hb : d83662 q = 1) : d7634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6118, d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6118, d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9853 (p : Pattern) (ha : d6124 p = 1) (hb : d83662 p = 1) : d84761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d83662 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6119 q = 1) (hb : d83662 q = 1) : d84756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9852 q ha hb
    | true =>
      simp only [d6119, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6120 q = 1) (hb : d83662 q = 1) : d84757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6121 q = 1) (hb : d83662 q = 1) : d84758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6121, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6122 q = 1) (hb : d83662 q = 1) : d84759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6123 q = 1) (hb : d83662 q = 1) : d84760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6124 q = 1) (hb : d83662 q = 1) : d84761 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6124, d84761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6124, d84761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9854 (p : Pattern) (ha : d6127 p = 1) (hb : d83662 p = 1) : d7655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6115 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6117 q = 1) (hb : d83662 q = 1) : d7633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6117, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6127 q = 1) (hb : d83662 q = 1) : d7655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6127, d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6127, d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9855 (p : Pattern) (ha : d6133 p = 1) (hb : d83662 p = 1) : d84769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d83662 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6119 q = 1) (hb : d83662 q = 1) : d84756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9852 q ha hb
    | true =>
      simp only [d6119, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6120 q = 1) (hb : d83662 q = 1) : d84757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6121 q = 1) (hb : d83662 q = 1) : d84758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6121, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6122 q = 1) (hb : d83662 q = 1) : d84759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6123 q = 1) (hb : d83662 q = 1) : d84760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d83662 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6128 q = 1) (hb : d83662 q = 1) : d84764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d84764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9854 q ha hb
    | true =>
      simp only [d6128, d84764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6129 q = 1) (hb : d83662 q = 1) : d84765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d84765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6129, d84765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6130 q = 1) (hb : d83662 q = 1) : d84766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d84766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6130, d84766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6131 q = 1) (hb : d83662 q = 1) : d84767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d84767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d84767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6132 q = 1) (hb : d83662 q = 1) : d84768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d84768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d84768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6133 q = 1) (hb : d83662 q = 1) : d84769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6133, d84769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6133, d84769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9856 (p : Pattern) (ha : d4919 p = 1) (hb : d77842 p = 1) : d7575 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d766 q = 1) : d766 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4918 q = 1) (hb : d77842 q = 1) : d7574 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d4918, d77842, d7574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4918, d77842, d7574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4919 q = 1) (hb : d77842 q = 1) : d7575 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d4919, d7575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4919, d7575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9857 (p : Pattern) (ha : d4925 p = 1) (hb : d83662 p = 1) : d7634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4920 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9856 q ha hb
    | true =>
      simp only [d4920, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4921 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4921, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4922 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4922, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4923 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4923, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4924 q = 1) (hb : d83662 q = 1) : d7633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4924, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4925 q = 1) (hb : d83662 q = 1) : d7634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4925, d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4925, d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9858 (p : Pattern) (ha : d6193 p = 1) (hb : d83662 p = 1) : d84812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d83662 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6188 q = 1) (hb : d83662 q = 1) : d84756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6188, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9857 q ha hb
    | true =>
      simp only [d6188, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6189 q = 1) (hb : d83662 q = 1) : d84757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6189, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6189, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6190 q = 1) (hb : d83662 q = 1) : d84758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6190, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6190, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6191 q = 1) (hb : d83662 q = 1) : d84759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6191, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6191, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6192 q = 1) (hb : d83662 q = 1) : d84760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6192, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6192, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d83662 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6193 q = 1) (hb : d83662 q = 1) : d84812 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6193, d84812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6193, d84812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9859 (p : Pattern) (ha : d6138 p = 1) (hb : d83662 p = 1) : d84774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6137 q = 1) (hb : d83662 q = 1) : d84773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6137, d84773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6137, d84773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6138 q = 1) (hb : d83662 q = 1) : d84774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6138, d84774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6138, d84774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9860 (p : Pattern) (ha : d6145 p = 1) (hb : d83662 p = 1) : d84781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6143 q = 1) (hb : d83662 q = 1) : d84779 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6143, d84779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6143, d84779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6144 q = 1) (hb : d83662 q = 1) : d84780 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6144, d84780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6144, d84780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6145 q = 1) (hb : d83662 q = 1) : d84781 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6145, d84781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6145, d84781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9861 (p : Pattern) (ha : d845 p = 1) (hb : d77842 p = 1) : d7613 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d843 q = 1) : d843 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d844 q = 1) (hb : d77842 q = 1) : d7612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d844, d77842, d7612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d844, d77842, d7612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d845 q = 1) (hb : d77842 q = 1) : d7613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d845, d7613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d845, d7613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9862 (p : Pattern) (ha : d6152 p = 1) (hb : d83662 p = 1) : d84788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d846 q = 1) (hb : d77842 q = 1) : d7614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d7614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9861 q ha hb
    | true =>
      simp only [d846, d7614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d847 q = 1) (hb : d77842 q = 1) : d7615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d7615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d847, d7615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6149 q = 1) (hb : d83662 q = 1) : d84785 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6149, d83662, d84785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6149, d83662, d84785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6150 q = 1) (hb : d83662 q = 1) : d84786 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6150, d84786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6150, d84786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6151 q = 1) (hb : d83662 q = 1) : d84787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6151, d84787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6151, d84787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6152 q = 1) (hb : d83662 q = 1) : d84788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6152, d84788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6152, d84788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9863 (p : Pattern) (ha : d76904 p = 1) (hb : d83662 p = 1) : d84794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d83662 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6139 q = 1) (hb : d83662 q = 1) : d84775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d84775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9859 q ha hb
    | true =>
      simp only [d6139, d84775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6140 q = 1) (hb : d83662 q = 1) : d84776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d84776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d84776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6141 q = 1) (hb : d83662 q = 1) : d84777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d84777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6141, d84777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6142 q = 1) (hb : d83662 q = 1) : d84778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d84778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d84778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d83662 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6146 q = 1) (hb : d83662 q = 1) : d84782 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d84782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9860 q ha hb
    | true =>
      simp only [d6146, d84782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6147 q = 1) (hb : d83662 q = 1) : d84783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d84783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d84783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6148 q = 1) (hb : d83662 q = 1) : d84784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d84784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6148, d84784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6153 q = 1) (hb : d83662 q = 1) : d84789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d84789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9862 q ha hb
    | true =>
      simp only [d6153, d84789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9857 q ha hb
  have h11 (q : Pattern) (ha : d76900 q = 1) (hb : d83662 q = 1) : d84790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d84790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76900, d84790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6160 q = 1) (hb : d83662 q = 1) : d7635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d7635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9852 q ha hb
    | true =>
      simp only [d6160, d7635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6161 q = 1) (hb : d83662 q = 1) : d7636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6161, d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76901 q = 1) (hb : d83662 q = 1) : d84791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d84791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76901, d84791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76902 q = 1) (hb : d83662 q = 1) : d84792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d84792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76902, d84792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76903 q = 1) (hb : d83662 q = 1) : d84793 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d84793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76903, d84793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76904 q = 1) (hb : d83662 q = 1) : d84794 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76904, d84794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76904, d84794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro9864 (p : Pattern) (ha : d6166 p = 1) (hb : d83662 p = 1) : d84795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6137 q = 1) (hb : d83662 q = 1) : d84773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6137, d84773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6137, d84773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6166 q = 1) (hb : d83662 q = 1) : d84795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6166, d84795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6166, d84795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9865 (p : Pattern) (ha : d6171 p = 1) (hb : d83662 p = 1) : d84800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6143 q = 1) (hb : d83662 q = 1) : d84779 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6143, d84779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6143, d84779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6144 q = 1) (hb : d83662 q = 1) : d84780 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6144, d84780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6144, d84780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6171 q = 1) (hb : d83662 q = 1) : d84800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6171, d84800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6171, d84800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9866 (p : Pattern) (ha : d6175 p = 1) (hb : d83662 p = 1) : d84804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d77842 q = 1) : d7614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d7614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9861 q ha hb
    | true =>
      simp only [d846, d7614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d77842 q = 1) : d7615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d7615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d7615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6149 q = 1) (hb : d83662 q = 1) : d84785 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6149, d83662, d84785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6149, d83662, d84785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6150 q = 1) (hb : d83662 q = 1) : d84786 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6150, d84786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6150, d84786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6151 q = 1) (hb : d83662 q = 1) : d84787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6151, d84787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6151, d84787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6175 q = 1) (hb : d83662 q = 1) : d84804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6175, d84804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6175, d84804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9867 (p : Pattern) (ha : d6176 p = 1) (hb : d83662 p = 1) : d7655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4920 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9856 q ha hb
    | true =>
      simp only [d4920, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4921 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4921, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4922 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4922, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4923 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4923, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4924 q = 1) (hb : d83662 q = 1) : d7633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4924, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6176 q = 1) (hb : d83662 q = 1) : d7655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6176, d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6176, d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9868 (p : Pattern) (ha : d76909 p = 1) (hb : d83662 p = 1) : d84810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d83662 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6139 q = 1) (hb : d83662 q = 1) : d84775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d84775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9859 q ha hb
    | true =>
      simp only [d6139, d84775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6140 q = 1) (hb : d83662 q = 1) : d84776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d84776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d84776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6141 q = 1) (hb : d83662 q = 1) : d84777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d84777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6141, d84777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6142 q = 1) (hb : d83662 q = 1) : d84778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d84778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d84778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d83662 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6146 q = 1) (hb : d83662 q = 1) : d84782 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d84782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9860 q ha hb
    | true =>
      simp only [d6146, d84782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6147 q = 1) (hb : d83662 q = 1) : d84783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d84783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d84783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6148 q = 1) (hb : d83662 q = 1) : d84784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d84784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6148, d84784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6153 q = 1) (hb : d83662 q = 1) : d84789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d84789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9862 q ha hb
    | true =>
      simp only [d6153, d84789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9857 q ha hb
  have h11 (q : Pattern) (ha : d76900 q = 1) (hb : d83662 q = 1) : d84790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76900, d84790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76900, d84790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6160 q = 1) (hb : d83662 q = 1) : d7635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d7635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9852 q ha hb
    | true =>
      simp only [d6160, d7635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6161 q = 1) (hb : d83662 q = 1) : d7636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6161, d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76901 q = 1) (hb : d83662 q = 1) : d84791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76901, d84791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76901, d84791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76902 q = 1) (hb : d83662 q = 1) : d84792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76902, d84792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76902, d84792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76903 q = 1) (hb : d83662 q = 1) : d84793 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76903, d84793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76903, d84793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d916 q = 1) (hb : d83662 q = 1) : d916 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6167 q = 1) (hb : d83662 q = 1) : d84796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6167, d84796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9864 q ha hb
    | true =>
      simp only [d6167, d84796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6168 q = 1) (hb : d83662 q = 1) : d84797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6168, d84797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6168, d84797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6169 q = 1) (hb : d83662 q = 1) : d84798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6169, d84798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6169, d84798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6170 q = 1) (hb : d83662 q = 1) : d84799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6170, d84799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6170, d84799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d922 q = 1) (hb : d83662 q = 1) : d922 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6172 q = 1) (hb : d83662 q = 1) : d84801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6172, d84801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9865 q ha hb
    | true =>
      simp only [d6172, d84801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6173 q = 1) (hb : d83662 q = 1) : d84802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6173, d84802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6173, d84802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6174 q = 1) (hb : d83662 q = 1) : d84803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6174, d84803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6174, d84803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6177 q = 1) (hb : d83662 q = 1) : d84805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d84805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9866 q ha hb
    | true =>
      simp only [d6177, d84805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9867 q ha hb
  have h27 (q : Pattern) (ha : d76905 q = 1) (hb : d83662 q = 1) : d84806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d84806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76905, d84806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6181 q = 1) (hb : d83662 q = 1) : d7656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d7656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9854 q ha hb
    | true =>
      simp only [d6181, d7656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6182 q = 1) (hb : d83662 q = 1) : d7657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6182, d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76906 q = 1) (hb : d83662 q = 1) : d84807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d84807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76906, d84807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76907 q = 1) (hb : d83662 q = 1) : d84808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76907, d84808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76907, d84808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76908 q = 1) (hb : d83662 q = 1) : d84809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76908, d84809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76908, d84809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76909 q = 1) (hb : d83662 q = 1) : d84810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76909, d84810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76909, d84810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro9869 (p : Pattern) (ha : d76916 p = 1) (hb : d83662 p = 1) : d84819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6177 q = 1) (hb : d83662 q = 1) : d84805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d84805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9866 q ha hb
    | true =>
      simp only [d6177, d84805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9867 q ha hb
  have h2 (q : Pattern) (ha : d76905 q = 1) (hb : d83662 q = 1) : d84806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76905, d84806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76905, d84806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6181 q = 1) (hb : d83662 q = 1) : d7656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d7656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9854 q ha hb
    | true =>
      simp only [d6181, d7656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6182 q = 1) (hb : d83662 q = 1) : d7657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6182, d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76906 q = 1) (hb : d83662 q = 1) : d84807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76906, d84807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76906, d84807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76914 q = 1) (hb : d83662 q = 1) : d84817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76914, d84817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76914, d84817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76915 q = 1) (hb : d83662 q = 1) : d84818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76915, d84818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76915, d84818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76916 q = 1) (hb : d83662 q = 1) : d84819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76916, d84819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76916, d84819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9870 (p : Pattern) (ha : d992 p = 1) (hb : d77842 p = 1) : d7677 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d985 q = 1) : d985 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d990 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d991 q = 1) (hb : d77842 q = 1) : d7676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d991, d77842, d7676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d991, d77842, d7676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d992 q = 1) (hb : d77842 q = 1) : d7677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d992, d7677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d992, d7677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9871 (p : Pattern) (ha : d6209 p = 1) (hb : d83662 p = 1) : d84828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d77842 q = 1) : d7678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d7678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9870 q ha hb
    | true =>
      simp only [d993, d7678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d77842 q = 1) : d7679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d7679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d7679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6206 q = 1) (hb : d83662 q = 1) : d84825 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6206, d83662, d84825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6206, d83662, d84825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6207 q = 1) (hb : d83662 q = 1) : d84826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6207, d84826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6207, d84826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6208 q = 1) (hb : d83662 q = 1) : d84827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6208, d84827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6208, d84827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6209 q = 1) (hb : d83662 q = 1) : d84828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6209, d84828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6209, d84828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9872 (p : Pattern) (ha : d6216 p = 1) (hb : d77842 p = 1) : d7681 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d990 q = 1) : d990 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6215 q = 1) (hb : d77842 q = 1) : d7680 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6215, d77842, d7680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6215, d77842, d7680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6216 q = 1) (hb : d77842 q = 1) : d7681 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6216, d7681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6216, d7681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9873 (p : Pattern) (ha : d6222 p = 1) (hb : d83662 p = 1) : d7706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6217 q = 1) (hb : d77842 q = 1) : d7682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9872 q ha hb
    | true =>
      simp only [d6217, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6218 q = 1) (hb : d77842 q = 1) : d7683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6218, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6218, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6219 q = 1) (hb : d83662 q = 1) : d7703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6219, d83662, d7703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6219, d83662, d7703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6220 q = 1) (hb : d83662 q = 1) : d7704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6220, d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6220, d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6221 q = 1) (hb : d83662 q = 1) : d7705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6221, d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6221, d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6222 q = 1) (hb : d83662 q = 1) : d7706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6222, d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6222, d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9874 (p : Pattern) (ha : d6233 p = 1) (hb : d83662 p = 1) : d7706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d77842 q = 1) : d7682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8227 q ha hb
    | true =>
      simp only [d998, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d77842 q = 1) : d7683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6230 q = 1) (hb : d83662 q = 1) : d7703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6230, d83662, d7703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6230, d83662, d7703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6231 q = 1) (hb : d83662 q = 1) : d7704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6231, d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6231, d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6232 q = 1) (hb : d83662 q = 1) : d7705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6232, d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6232, d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6233 q = 1) (hb : d83662 q = 1) : d7706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6233, d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6233, d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9875 (p : Pattern) (ha : d76926 p = 1) (hb : d83662 p = 1) : d84834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6223 q = 1) (hb : d83662 q = 1) : d84829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6223, d84829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9871 q ha hb
    | true =>
      simp only [d6223, d84829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9873 q ha hb
  have h2 (q : Pattern) (ha : d76922 q = 1) (hb : d83662 q = 1) : d84830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76922, d84830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76922, d84830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6234 q = 1) (hb : d83662 q = 1) : d7707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d7707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9874 q ha hb
    | true =>
      simp only [d6234, d7707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6235 q = 1) (hb : d83662 q = 1) : d7708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, d7708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6235, d7708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76923 q = 1) (hb : d83662 q = 1) : d84831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76923, d84831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76923, d84831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76924 q = 1) (hb : d83662 q = 1) : d84832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76924, d84832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76924, d84832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76925 q = 1) (hb : d83662 q = 1) : d84833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76925, d84833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76925, d84833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76926 q = 1) (hb : d83662 q = 1) : d84834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76926, d84834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76926, d84834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9876 (p : Pattern) (ha : d76932 p = 1) (hb : d83662 p = 1) : d84840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6125 q = 1) (hb : d83662 q = 1) : d84762 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6125, d84762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6125, d84762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9853 q ha hb
  have h2 (q : Pattern) (ha : d6126 q = 1) (hb : d83662 q = 1) : d84763 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6126, d84763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6126, d84763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6134 q = 1) (hb : d83662 q = 1) : d84770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d84770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9853 q ha hb
    | true =>
      simp only [d6134, d84770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9855 q ha hb
  have h4 (q : Pattern) (ha : d6135 q = 1) (hb : d83662 q = 1) : d84771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d84771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6135, d84771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6136 q = 1) (hb : d83662 q = 1) : d84772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6136, d84772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6136, d84772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76910 q = 1) (hb : d83662 q = 1) : d84811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76910, d84811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9863 q ha hb
    | true =>
      simp only [d76910, d84811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9868 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d83662 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6194 q = 1) (hb : d83662 q = 1) : d84813 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6194, d84813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9858 q ha hb
    | true =>
      simp only [d6194, d84813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76911 q = 1) (hb : d83662 q = 1) : d84814 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76911, d84814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76911, d84814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76912 q = 1) (hb : d83662 q = 1) : d84815 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76912, d84815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76912, d84815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76913 q = 1) (hb : d83662 q = 1) : d84816 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76913, d84816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76913, d84816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76917 q = 1) (hb : d83662 q = 1) : d84820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76917, d84820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76917, d84820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9869 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d83662 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d76918 q = 1) (hb : d83662 q = 1) : d84821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76918, d84821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76918, d84821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76919 q = 1) (hb : d83662 q = 1) : d84822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76919, d84822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76919, d84822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76920 q = 1) (hb : d83662 q = 1) : d84823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76920, d84823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76920, d84823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d76921 q = 1) (hb : d83662 q = 1) : d84824 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76921, d84824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76921, d84824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76927 q = 1) (hb : d83662 q = 1) : d84835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76927, d84835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76927, d84835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9875 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d83662 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d76928 q = 1) (hb : d83662 q = 1) : d84836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76928, d84836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76928, d84836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d76929 q = 1) (hb : d83662 q = 1) : d84837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76929, d84837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76929, d84837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76930 q = 1) (hb : d83662 q = 1) : d84838 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76930, d84838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76930, d84838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76931 q = 1) (hb : d83662 q = 1) : d84839 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76931, d84839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76931, d84839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d76932 q = 1) (hb : d83662 q = 1) : d84840 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76932, d84840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76932, d84840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro9877 (p : Pattern) (ha : d76938 p = 1) (hb : d83662 p = 1) : d84846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76933 q = 1) (hb : d83662 q = 1) : d84841 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76933, d84841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76933, d84841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9876 q ha hb
  have h2 (q : Pattern) (ha : d76934 q = 1) (hb : d83662 q = 1) : d84842 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76934, d84842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76934, d84842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76935 q = 1) (hb : d83662 q = 1) : d84843 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76935, d84843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76935, d84843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76936 q = 1) (hb : d83662 q = 1) : d84844 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76936, d84844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76936, d84844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76937 q = 1) (hb : d83662 q = 1) : d84845 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76937, d84845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76937, d84845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76938 q = 1) (hb : d83662 q = 1) : d84846 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76938, d84846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76938, d84846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9878 (p : Pattern) (ha : d6257 p = 1) (hb : d83662 p = 1) : d7787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6256 q = 1) (hb : d83662 q = 1) : d7786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6256, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6257 q = 1) (hb : d83662 q = 1) : d7787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6257, d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6257, d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9879 (p : Pattern) (ha : d6263 p = 1) (hb : d83662 p = 1) : d84854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d83662 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6258 q = 1) (hb : d83662 q = 1) : d84849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9878 q ha hb
    | true =>
      simp only [d6258, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6259 q = 1) (hb : d83662 q = 1) : d84850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6260 q = 1) (hb : d83662 q = 1) : d84851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6260, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6261 q = 1) (hb : d83662 q = 1) : d84852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6262 q = 1) (hb : d83662 q = 1) : d84853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6263 q = 1) (hb : d83662 q = 1) : d84854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, d84854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6263, d84854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9880 (p : Pattern) (ha : d6266 p = 1) (hb : d83662 p = 1) : d7808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6254 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6256 q = 1) (hb : d83662 q = 1) : d7786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6256, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6266 q = 1) (hb : d83662 q = 1) : d7808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6266, d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6266, d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9881 (p : Pattern) (ha : d6272 p = 1) (hb : d83662 p = 1) : d84862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d83662 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6258 q = 1) (hb : d83662 q = 1) : d84849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9878 q ha hb
    | true =>
      simp only [d6258, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6259 q = 1) (hb : d83662 q = 1) : d84850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6260 q = 1) (hb : d83662 q = 1) : d84851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6260, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6261 q = 1) (hb : d83662 q = 1) : d84852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6262 q = 1) (hb : d83662 q = 1) : d84853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d83662 q = 1) : d1172 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6267 q = 1) (hb : d83662 q = 1) : d84857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d84857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9880 q ha hb
    | true =>
      simp only [d6267, d84857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6268 q = 1) (hb : d83662 q = 1) : d84858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d84858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6268, d84858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6269 q = 1) (hb : d83662 q = 1) : d84859 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d84859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6269, d84859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6270 q = 1) (hb : d83662 q = 1) : d84860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d84860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d84860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6271 q = 1) (hb : d83662 q = 1) : d84861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d84861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d84861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6272 q = 1) (hb : d83662 q = 1) : d84862 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, d84862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6272, d84862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9882 (p : Pattern) (ha : d5029 p = 1) (hb : d77842 p = 1) : d7728 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1145 q = 1) : d1145 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5028 q = 1) (hb : d77842 q = 1) : d7727 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5028, d77842, d7727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5028, d77842, d7727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5029 q = 1) (hb : d77842 q = 1) : d7728 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5029, d7728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5029, d7728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9883 (p : Pattern) (ha : d5035 p = 1) (hb : d83662 p = 1) : d7787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5030 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9882 q ha hb
    | true =>
      simp only [d5030, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5031 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5031, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5032 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5032, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5033 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5033, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5034 q = 1) (hb : d83662 q = 1) : d7786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5034, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5035 q = 1) (hb : d83662 q = 1) : d7787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5035, d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5035, d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9884 (p : Pattern) (ha : d6332 p = 1) (hb : d83662 p = 1) : d84905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d83662 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6327 q = 1) (hb : d83662 q = 1) : d84849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6327, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9883 q ha hb
    | true =>
      simp only [d6327, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6328 q = 1) (hb : d83662 q = 1) : d84850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6328, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6328, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6329 q = 1) (hb : d83662 q = 1) : d84851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6329, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6329, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6330 q = 1) (hb : d83662 q = 1) : d84852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6330, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6330, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6331 q = 1) (hb : d83662 q = 1) : d84853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6331, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6331, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d83662 q = 1) : d1354 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6332 q = 1) (hb : d83662 q = 1) : d84905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6332, d84905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6332, d84905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9885 (p : Pattern) (ha : d6277 p = 1) (hb : d83662 p = 1) : d84867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6276 q = 1) (hb : d83662 q = 1) : d84866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6276, d84866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6276, d84866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6277 q = 1) (hb : d83662 q = 1) : d84867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6277, d84867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6277, d84867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9886 (p : Pattern) (ha : d6284 p = 1) (hb : d83662 p = 1) : d84874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6282 q = 1) (hb : d83662 q = 1) : d84872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6282, d84872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6282, d84872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6283 q = 1) (hb : d83662 q = 1) : d84873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6283, d84873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6283, d84873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6284 q = 1) (hb : d83662 q = 1) : d84874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6284, d84874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6284, d84874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9887 (p : Pattern) (ha : d1221 p = 1) (hb : d77842 p = 1) : d7766 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1219 q = 1) : d1219 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1220 q = 1) (hb : d77842 q = 1) : d7765 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1220, d77842, d7765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1220, d77842, d7765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1221 q = 1) (hb : d77842 q = 1) : d7766 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1221, d7766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1221, d7766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9888 (p : Pattern) (ha : d6291 p = 1) (hb : d83662 p = 1) : d84881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1222 q = 1) (hb : d77842 q = 1) : d7767 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d7767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9887 q ha hb
    | true =>
      simp only [d1222, d7767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1223 q = 1) (hb : d77842 q = 1) : d7768 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d7768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1223, d7768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6288 q = 1) (hb : d83662 q = 1) : d84878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6288, d83662, d84878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6288, d83662, d84878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6289 q = 1) (hb : d83662 q = 1) : d84879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6289, d84879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6289, d84879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6290 q = 1) (hb : d83662 q = 1) : d84880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6290, d84880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6290, d84880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6291 q = 1) (hb : d83662 q = 1) : d84881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6291, d84881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6291, d84881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9889 (p : Pattern) (ha : d76945 p = 1) (hb : d83662 p = 1) : d84887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d83662 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6278 q = 1) (hb : d83662 q = 1) : d84868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d84868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9885 q ha hb
    | true =>
      simp only [d6278, d84868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6279 q = 1) (hb : d83662 q = 1) : d84869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d84869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d84869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6280 q = 1) (hb : d83662 q = 1) : d84870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d84870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6280, d84870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6281 q = 1) (hb : d83662 q = 1) : d84871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d84871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d84871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d83662 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6285 q = 1) (hb : d83662 q = 1) : d84875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d84875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9886 q ha hb
    | true =>
      simp only [d6285, d84875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6286 q = 1) (hb : d83662 q = 1) : d84876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d84876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d84876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6287 q = 1) (hb : d83662 q = 1) : d84877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d84877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6287, d84877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6292 q = 1) (hb : d83662 q = 1) : d84882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d84882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9888 q ha hb
    | true =>
      simp only [d6292, d84882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9883 q ha hb
  have h11 (q : Pattern) (ha : d76941 q = 1) (hb : d83662 q = 1) : d84883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d84883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76941, d84883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6299 q = 1) (hb : d83662 q = 1) : d7788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d7788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9878 q ha hb
    | true =>
      simp only [d6299, d7788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6300 q = 1) (hb : d83662 q = 1) : d7789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6300, d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76942 q = 1) (hb : d83662 q = 1) : d84884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d84884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76942, d84884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76943 q = 1) (hb : d83662 q = 1) : d84885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d84885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76943, d84885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76944 q = 1) (hb : d83662 q = 1) : d84886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d84886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76944, d84886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76945 q = 1) (hb : d83662 q = 1) : d84887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76945, d84887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76945, d84887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro9890 (p : Pattern) (ha : d6305 p = 1) (hb : d83662 p = 1) : d84888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6276 q = 1) (hb : d83662 q = 1) : d84866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6276, d84866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6276, d84866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6305 q = 1) (hb : d83662 q = 1) : d84888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6305, d84888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6305, d84888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9891 (p : Pattern) (ha : d6310 p = 1) (hb : d83662 p = 1) : d84893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6282 q = 1) (hb : d83662 q = 1) : d84872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6282, d84872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6282, d84872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6283 q = 1) (hb : d83662 q = 1) : d84873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6283, d84873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6283, d84873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6310 q = 1) (hb : d83662 q = 1) : d84893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6310, d84893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6310, d84893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9892 (p : Pattern) (ha : d6314 p = 1) (hb : d83662 p = 1) : d84897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d77842 q = 1) : d7767 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d7767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9887 q ha hb
    | true =>
      simp only [d1222, d7767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d77842 q = 1) : d7768 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d7768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d7768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6288 q = 1) (hb : d83662 q = 1) : d84878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6288, d83662, d84878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6288, d83662, d84878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6289 q = 1) (hb : d83662 q = 1) : d84879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6289, d84879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6289, d84879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6290 q = 1) (hb : d83662 q = 1) : d84880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6290, d84880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6290, d84880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6314 q = 1) (hb : d83662 q = 1) : d84897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6314, d84897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6314, d84897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9893 (p : Pattern) (ha : d6315 p = 1) (hb : d83662 p = 1) : d7808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5030 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9882 q ha hb
    | true =>
      simp only [d5030, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5031 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5031, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5032 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5032, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5033 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5033, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5034 q = 1) (hb : d83662 q = 1) : d7786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5034, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6315 q = 1) (hb : d83662 q = 1) : d7808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6315, d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6315, d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9894 (p : Pattern) (ha : d76950 p = 1) (hb : d83662 p = 1) : d84903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d83662 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6278 q = 1) (hb : d83662 q = 1) : d84868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d84868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9885 q ha hb
    | true =>
      simp only [d6278, d84868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6279 q = 1) (hb : d83662 q = 1) : d84869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d84869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d84869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6280 q = 1) (hb : d83662 q = 1) : d84870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d84870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6280, d84870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6281 q = 1) (hb : d83662 q = 1) : d84871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d84871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d84871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d83662 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6285 q = 1) (hb : d83662 q = 1) : d84875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d84875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9886 q ha hb
    | true =>
      simp only [d6285, d84875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6286 q = 1) (hb : d83662 q = 1) : d84876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d84876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d84876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6287 q = 1) (hb : d83662 q = 1) : d84877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d84877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6287, d84877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6292 q = 1) (hb : d83662 q = 1) : d84882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d84882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9888 q ha hb
    | true =>
      simp only [d6292, d84882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9883 q ha hb
  have h11 (q : Pattern) (ha : d76941 q = 1) (hb : d83662 q = 1) : d84883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76941, d84883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76941, d84883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6299 q = 1) (hb : d83662 q = 1) : d7788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d7788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9878 q ha hb
    | true =>
      simp only [d6299, d7788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6300 q = 1) (hb : d83662 q = 1) : d7789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6300, d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76942 q = 1) (hb : d83662 q = 1) : d84884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76942, d84884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76942, d84884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76943 q = 1) (hb : d83662 q = 1) : d84885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76943, d84885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76943, d84885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76944 q = 1) (hb : d83662 q = 1) : d84886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76944, d84886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76944, d84886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1327 q = 1) (hb : d83662 q = 1) : d1327 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6306 q = 1) (hb : d83662 q = 1) : d84889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6306, d84889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9890 q ha hb
    | true =>
      simp only [d6306, d84889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6307 q = 1) (hb : d83662 q = 1) : d84890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6307, d84890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6307, d84890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6308 q = 1) (hb : d83662 q = 1) : d84891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6308, d84891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6308, d84891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6309 q = 1) (hb : d83662 q = 1) : d84892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6309, d84892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6309, d84892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1333 q = 1) (hb : d83662 q = 1) : d1333 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6311 q = 1) (hb : d83662 q = 1) : d84894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6311, d84894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9891 q ha hb
    | true =>
      simp only [d6311, d84894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6312 q = 1) (hb : d83662 q = 1) : d84895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6312, d84895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6312, d84895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6313 q = 1) (hb : d83662 q = 1) : d84896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6313, d84896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6313, d84896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6316 q = 1) (hb : d83662 q = 1) : d84898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d84898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9892 q ha hb
    | true =>
      simp only [d6316, d84898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9893 q ha hb
  have h27 (q : Pattern) (ha : d76946 q = 1) (hb : d83662 q = 1) : d84899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d84899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76946, d84899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6320 q = 1) (hb : d83662 q = 1) : d7809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d7809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9880 q ha hb
    | true =>
      simp only [d6320, d7809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6321 q = 1) (hb : d83662 q = 1) : d7810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6321, d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76947 q = 1) (hb : d83662 q = 1) : d84900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d84900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76947, d84900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76948 q = 1) (hb : d83662 q = 1) : d84901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76948, d84901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76948, d84901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76949 q = 1) (hb : d83662 q = 1) : d84902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76949, d84902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76949, d84902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76950 q = 1) (hb : d83662 q = 1) : d84903 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76950, d84903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76950, d84903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro9895 (p : Pattern) (ha : d76957 p = 1) (hb : d83662 p = 1) : d84912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6316 q = 1) (hb : d83662 q = 1) : d84898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d84898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9892 q ha hb
    | true =>
      simp only [d6316, d84898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9893 q ha hb
  have h2 (q : Pattern) (ha : d76946 q = 1) (hb : d83662 q = 1) : d84899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76946, d84899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76946, d84899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6320 q = 1) (hb : d83662 q = 1) : d7809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d7809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9880 q ha hb
    | true =>
      simp only [d6320, d7809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6321 q = 1) (hb : d83662 q = 1) : d7810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6321, d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76947 q = 1) (hb : d83662 q = 1) : d84900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76947, d84900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76947, d84900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76955 q = 1) (hb : d83662 q = 1) : d84910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76955, d84910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76955, d84910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76956 q = 1) (hb : d83662 q = 1) : d84911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76956, d84911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76956, d84911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76957 q = 1) (hb : d83662 q = 1) : d84912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76957, d84912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76957, d84912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9896 (p : Pattern) (ha : d1417 p = 1) (hb : d77842 p = 1) : d7830 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1405 q = 1) : d1405 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1415 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1416 q = 1) (hb : d77842 q = 1) : d7829 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1416, d77842, d7829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1416, d77842, d7829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1417 q = 1) (hb : d77842 q = 1) : d7830 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1417, d7830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1417, d7830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9897 (p : Pattern) (ha : d6348 p = 1) (hb : d83662 p = 1) : d84921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d77842 q = 1) : d7831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d7831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9896 q ha hb
    | true =>
      simp only [d1418, d7831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d77842 q = 1) : d7832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d7832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d7832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6345 q = 1) (hb : d83662 q = 1) : d84918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6345, d83662, d84918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6345, d83662, d84918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6346 q = 1) (hb : d83662 q = 1) : d84919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6346, d84919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6346, d84919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6347 q = 1) (hb : d83662 q = 1) : d84920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6347, d84920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6347, d84920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6348 q = 1) (hb : d83662 q = 1) : d84921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6348, d84921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6348, d84921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9898 (p : Pattern) (ha : d6361 p = 1) (hb : d77842 p = 1) : d7834 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1415 q = 1) : d1415 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6360 q = 1) (hb : d77842 q = 1) : d7833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6360, d77842, d7833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6360, d77842, d7833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6361 q = 1) (hb : d77842 q = 1) : d7834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6361, d7834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6361, d7834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9899 (p : Pattern) (ha : d6367 p = 1) (hb : d83662 p = 1) : d7859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6362 q = 1) (hb : d77842 q = 1) : d7835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9898 q ha hb
    | true =>
      simp only [d6362, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6363 q = 1) (hb : d77842 q = 1) : d7836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6363, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6363, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6364 q = 1) (hb : d83662 q = 1) : d7856 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6364, d83662, d7856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6364, d83662, d7856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6365 q = 1) (hb : d83662 q = 1) : d7857 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6365, d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6365, d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6366 q = 1) (hb : d83662 q = 1) : d7858 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6366, d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6366, d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6367 q = 1) (hb : d83662 q = 1) : d7859 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6367, d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6367, d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9900 (p : Pattern) (ha : d6378 p = 1) (hb : d83662 p = 1) : d7859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d77842 q = 1) : d7835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8255 q ha hb
    | true =>
      simp only [d1423, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d77842 q = 1) : d7836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6375 q = 1) (hb : d83662 q = 1) : d7856 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6375, d83662, d7856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6375, d83662, d7856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6376 q = 1) (hb : d83662 q = 1) : d7857 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6376, d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6376, d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6377 q = 1) (hb : d83662 q = 1) : d7858 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6377, d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6377, d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6378 q = 1) (hb : d83662 q = 1) : d7859 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6378, d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6378, d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9901 (p : Pattern) (ha : d76967 p = 1) (hb : d83662 p = 1) : d84927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6368 q = 1) (hb : d83662 q = 1) : d84922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6368, d84922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9897 q ha hb
    | true =>
      simp only [d6368, d84922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9899 q ha hb
  have h2 (q : Pattern) (ha : d76963 q = 1) (hb : d83662 q = 1) : d84923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76963, d84923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76963, d84923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6379 q = 1) (hb : d83662 q = 1) : d7860 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d7860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9900 q ha hb
    | true =>
      simp only [d6379, d7860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6380 q = 1) (hb : d83662 q = 1) : d7861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, d7861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6380, d7861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76964 q = 1) (hb : d83662 q = 1) : d84924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76964, d84924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76964, d84924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76965 q = 1) (hb : d83662 q = 1) : d84925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76965, d84925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76965, d84925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76966 q = 1) (hb : d83662 q = 1) : d84926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76966, d84926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76966, d84926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76967 q = 1) (hb : d83662 q = 1) : d84927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76967, d84927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76967, d84927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9902 (p : Pattern) (ha : d76973 p = 1) (hb : d83662 p = 1) : d84933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6264 q = 1) (hb : d83662 q = 1) : d84855 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6264, d84855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6264, d84855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9879 q ha hb
  have h2 (q : Pattern) (ha : d6265 q = 1) (hb : d83662 q = 1) : d84856 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6265, d84856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6265, d84856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6273 q = 1) (hb : d83662 q = 1) : d84863 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d84863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9879 q ha hb
    | true =>
      simp only [d6273, d84863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9881 q ha hb
  have h4 (q : Pattern) (ha : d6274 q = 1) (hb : d83662 q = 1) : d84864 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d84864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6274, d84864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6275 q = 1) (hb : d83662 q = 1) : d84865 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6275, d84865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6275, d84865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76951 q = 1) (hb : d83662 q = 1) : d84904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76951, d84904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9889 q ha hb
    | true =>
      simp only [d76951, d84904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9894 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d83662 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6333 q = 1) (hb : d83662 q = 1) : d84906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6333, d84906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9884 q ha hb
    | true =>
      simp only [d6333, d84906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76952 q = 1) (hb : d83662 q = 1) : d84907 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76952, d84907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76952, d84907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76953 q = 1) (hb : d83662 q = 1) : d84908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76953, d84908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76953, d84908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76954 q = 1) (hb : d83662 q = 1) : d84909 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76954, d84909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76954, d84909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d76958 q = 1) (hb : d83662 q = 1) : d84913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76958, d84913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76958, d84913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9895 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d83662 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d76959 q = 1) (hb : d83662 q = 1) : d84914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76959, d84914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d76959, d84914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76960 q = 1) (hb : d83662 q = 1) : d84915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76960, d84915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76960, d84915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76961 q = 1) (hb : d83662 q = 1) : d84916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76961, d84916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76961, d84916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d76962 q = 1) (hb : d83662 q = 1) : d84917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76962, d84917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76962, d84917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d76968 q = 1) (hb : d83662 q = 1) : d84928 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76968, d84928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76968, d84928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9901 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d83662 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d76969 q = 1) (hb : d83662 q = 1) : d84929 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76969, d84929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d76969, d84929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d76970 q = 1) (hb : d83662 q = 1) : d84930 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76970, d84930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76970, d84930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d76971 q = 1) (hb : d83662 q = 1) : d84931 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76971, d84931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76971, d84931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d76972 q = 1) (hb : d83662 q = 1) : d84932 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76972, d84932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d76972, d84932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d76973 q = 1) (hb : d83662 q = 1) : d84933 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76973, d84933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76973, d84933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro9903 (p : Pattern) (ha : d76979 p = 1) (hb : d83662 p = 1) : d84939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76974 q = 1) (hb : d83662 q = 1) : d84934 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76974, d84934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76974, d84934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9902 q ha hb
  have h2 (q : Pattern) (ha : d76975 q = 1) (hb : d83662 q = 1) : d84935 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76975, d84935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76975, d84935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76976 q = 1) (hb : d83662 q = 1) : d84936 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76976, d84936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76976, d84936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76977 q = 1) (hb : d83662 q = 1) : d84937 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76977, d84937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76977, d84937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76978 q = 1) (hb : d83662 q = 1) : d84938 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76978, d84938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76978, d84938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76979 q = 1) (hb : d83662 q = 1) : d84939 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76979, d84939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76979, d84939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9904 (p : Pattern) (ha : d6403 p = 1) (hb : d83662 p = 1) : d7941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6402 q = 1) (hb : d83662 q = 1) : d7940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6402, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6403 q = 1) (hb : d83662 q = 1) : d7941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6403, d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6403, d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9905 (p : Pattern) (ha : d6409 p = 1) (hb : d83662 p = 1) : d84948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d83662 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6404 q = 1) (hb : d83662 q = 1) : d84943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9904 q ha hb
    | true =>
      simp only [d6404, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6405 q = 1) (hb : d83662 q = 1) : d84944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6406 q = 1) (hb : d83662 q = 1) : d84945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6406, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6407 q = 1) (hb : d83662 q = 1) : d84946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6408 q = 1) (hb : d83662 q = 1) : d84947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6409 q = 1) (hb : d83662 q = 1) : d84948 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, d84948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6409, d84948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9906 (p : Pattern) (ha : d6412 p = 1) (hb : d83662 p = 1) : d7962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6400 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6402 q = 1) (hb : d83662 q = 1) : d7940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6402, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6412 q = 1) (hb : d83662 q = 1) : d7962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6412, d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6412, d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9907 (p : Pattern) (ha : d6418 p = 1) (hb : d83662 p = 1) : d84956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d83662 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6404 q = 1) (hb : d83662 q = 1) : d84943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9904 q ha hb
    | true =>
      simp only [d6404, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6405 q = 1) (hb : d83662 q = 1) : d84944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6406 q = 1) (hb : d83662 q = 1) : d84945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6406, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6407 q = 1) (hb : d83662 q = 1) : d84946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6408 q = 1) (hb : d83662 q = 1) : d84947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d83662 q = 1) : d1633 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6413 q = 1) (hb : d83662 q = 1) : d84951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d84951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9906 q ha hb
    | true =>
      simp only [d6413, d84951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6414 q = 1) (hb : d83662 q = 1) : d84952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d84952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6414, d84952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6415 q = 1) (hb : d83662 q = 1) : d84953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d84953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6415, d84953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6416 q = 1) (hb : d83662 q = 1) : d84954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d84954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d84954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6417 q = 1) (hb : d83662 q = 1) : d84955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d84955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d84955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6418 q = 1) (hb : d83662 q = 1) : d84956 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, d84956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6418, d84956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9908 (p : Pattern) (ha : d5145 p = 1) (hb : d77842 p = 1) : d7882 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1606 q = 1) : d1606 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5144 q = 1) (hb : d77842 q = 1) : d7881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5144, d77842, d7881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5144, d77842, d7881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5145 q = 1) (hb : d77842 q = 1) : d7882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5145, d7882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5145, d7882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9909 (p : Pattern) (ha : d5151 p = 1) (hb : d83662 p = 1) : d7941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5146 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9908 q ha hb
    | true =>
      simp only [d5146, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5147 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5147, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5148 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5148, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5149 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5149, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5150 q = 1) (hb : d83662 q = 1) : d7940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5150, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5151 q = 1) (hb : d83662 q = 1) : d7941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5151, d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5151, d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9910 (p : Pattern) (ha : d6478 p = 1) (hb : d83662 p = 1) : d84999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d83662 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6473 q = 1) (hb : d83662 q = 1) : d84943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6473, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9909 q ha hb
    | true =>
      simp only [d6473, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6474 q = 1) (hb : d83662 q = 1) : d84944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6474, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6474, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6475 q = 1) (hb : d83662 q = 1) : d84945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6475, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6475, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6476 q = 1) (hb : d83662 q = 1) : d84946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6476, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6476, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6477 q = 1) (hb : d83662 q = 1) : d84947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6477, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6477, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d83662 q = 1) : d1831 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6478 q = 1) (hb : d83662 q = 1) : d84999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6478, d84999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6478, d84999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9911 (p : Pattern) (ha : d6423 p = 1) (hb : d83662 p = 1) : d84961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6422 q = 1) (hb : d83662 q = 1) : d84960 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6422, d84960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6422, d84960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6423 q = 1) (hb : d83662 q = 1) : d84961 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6423, d84961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6423, d84961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9912 (p : Pattern) (ha : d6430 p = 1) (hb : d83662 p = 1) : d84968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6428 q = 1) (hb : d83662 q = 1) : d84966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6428, d84966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6428, d84966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6429 q = 1) (hb : d83662 q = 1) : d84967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6429, d84967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6429, d84967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6430 q = 1) (hb : d83662 q = 1) : d84968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6430, d84968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6430, d84968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9913 (p : Pattern) (ha : d1676 p = 1) (hb : d77842 p = 1) : d7920 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1674 q = 1) : d1674 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1606 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1675 q = 1) (hb : d77842 q = 1) : d7919 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1675, d77842, d7919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1675, d77842, d7919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1676 q = 1) (hb : d77842 q = 1) : d7920 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1676, d7920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1676, d7920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9914 (p : Pattern) (ha : d6437 p = 1) (hb : d83662 p = 1) : d84975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1677 q = 1) (hb : d77842 q = 1) : d7921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d7921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9913 q ha hb
    | true =>
      simp only [d1677, d7921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1678 q = 1) (hb : d77842 q = 1) : d7922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d7922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1678, d7922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6434 q = 1) (hb : d83662 q = 1) : d84972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6434, d83662, d84972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6434, d83662, d84972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6435 q = 1) (hb : d83662 q = 1) : d84973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6435, d84973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6435, d84973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6436 q = 1) (hb : d83662 q = 1) : d84974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6436, d84974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6436, d84974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6437 q = 1) (hb : d83662 q = 1) : d84975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6437, d84975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6437, d84975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9915 (p : Pattern) (ha : d76987 p = 1) (hb : d83662 p = 1) : d84981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d83662 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6424 q = 1) (hb : d83662 q = 1) : d84962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d84962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9911 q ha hb
    | true =>
      simp only [d6424, d84962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6425 q = 1) (hb : d83662 q = 1) : d84963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d84963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d84963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6426 q = 1) (hb : d83662 q = 1) : d84964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d84964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6426, d84964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6427 q = 1) (hb : d83662 q = 1) : d84965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d84965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d84965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d83662 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6431 q = 1) (hb : d83662 q = 1) : d84969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d84969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9912 q ha hb
    | true =>
      simp only [d6431, d84969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6432 q = 1) (hb : d83662 q = 1) : d84970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d84970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d84970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6433 q = 1) (hb : d83662 q = 1) : d84971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d84971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6433, d84971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6438 q = 1) (hb : d83662 q = 1) : d84976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d84976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9914 q ha hb
    | true =>
      simp only [d6438, d84976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9909 q ha hb
  have h11 (q : Pattern) (ha : d76983 q = 1) (hb : d83662 q = 1) : d84977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d84977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76983, d84977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6445 q = 1) (hb : d83662 q = 1) : d7942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d7942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9904 q ha hb
    | true =>
      simp only [d6445, d7942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6446 q = 1) (hb : d83662 q = 1) : d7943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6446, d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76984 q = 1) (hb : d83662 q = 1) : d84978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d84978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76984, d84978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76985 q = 1) (hb : d83662 q = 1) : d84979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d84979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76985, d84979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76986 q = 1) (hb : d83662 q = 1) : d84980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d84980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76986, d84980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76987 q = 1) (hb : d83662 q = 1) : d84981 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76987, d84981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76987, d84981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro9916 (p : Pattern) (ha : d6451 p = 1) (hb : d83662 p = 1) : d84982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6422 q = 1) (hb : d83662 q = 1) : d84960 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6422, d84960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6422, d84960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6451 q = 1) (hb : d83662 q = 1) : d84982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6451, d84982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6451, d84982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9917 (p : Pattern) (ha : d6456 p = 1) (hb : d83662 p = 1) : d84987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6428 q = 1) (hb : d83662 q = 1) : d84966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6428, d84966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6428, d84966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6429 q = 1) (hb : d83662 q = 1) : d84967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6429, d84967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6429, d84967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6456 q = 1) (hb : d83662 q = 1) : d84987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6456, d84987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6456, d84987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9918 (p : Pattern) (ha : d6460 p = 1) (hb : d83662 p = 1) : d84991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d77842 q = 1) : d7921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d7921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9913 q ha hb
    | true =>
      simp only [d1677, d7921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d77842 q = 1) : d7922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d7922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d7922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6434 q = 1) (hb : d83662 q = 1) : d84972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6434, d83662, d84972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6434, d83662, d84972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6435 q = 1) (hb : d83662 q = 1) : d84973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6435, d84973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6435, d84973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6436 q = 1) (hb : d83662 q = 1) : d84974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6436, d84974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6436, d84974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6460 q = 1) (hb : d83662 q = 1) : d84991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6460, d84991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6460, d84991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9919 (p : Pattern) (ha : d6461 p = 1) (hb : d83662 p = 1) : d7962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5146 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9908 q ha hb
    | true =>
      simp only [d5146, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5147 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5147, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5148 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5148, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5149 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5149, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5150 q = 1) (hb : d83662 q = 1) : d7940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5150, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6461 q = 1) (hb : d83662 q = 1) : d7962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6461, d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6461, d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9920 (p : Pattern) (ha : d76992 p = 1) (hb : d83662 p = 1) : d84997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d83662 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6424 q = 1) (hb : d83662 q = 1) : d84962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d84962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9911 q ha hb
    | true =>
      simp only [d6424, d84962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6425 q = 1) (hb : d83662 q = 1) : d84963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d84963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d84963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6426 q = 1) (hb : d83662 q = 1) : d84964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d84964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6426, d84964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6427 q = 1) (hb : d83662 q = 1) : d84965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d84965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d84965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d83662 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6431 q = 1) (hb : d83662 q = 1) : d84969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d84969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9912 q ha hb
    | true =>
      simp only [d6431, d84969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6432 q = 1) (hb : d83662 q = 1) : d84970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d84970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d84970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6433 q = 1) (hb : d83662 q = 1) : d84971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d84971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6433, d84971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6438 q = 1) (hb : d83662 q = 1) : d84976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d84976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9914 q ha hb
    | true =>
      simp only [d6438, d84976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9909 q ha hb
  have h11 (q : Pattern) (ha : d76983 q = 1) (hb : d83662 q = 1) : d84977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76983, d84977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76983, d84977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6445 q = 1) (hb : d83662 q = 1) : d7942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d7942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9904 q ha hb
    | true =>
      simp only [d6445, d7942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6446 q = 1) (hb : d83662 q = 1) : d7943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6446, d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d76984 q = 1) (hb : d83662 q = 1) : d84978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76984, d84978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76984, d84978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76985 q = 1) (hb : d83662 q = 1) : d84979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76985, d84979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76985, d84979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76986 q = 1) (hb : d83662 q = 1) : d84980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76986, d84980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76986, d84980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1804 q = 1) (hb : d83662 q = 1) : d1804 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6452 q = 1) (hb : d83662 q = 1) : d84983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6452, d84983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9916 q ha hb
    | true =>
      simp only [d6452, d84983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6453 q = 1) (hb : d83662 q = 1) : d84984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6453, d84984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6453, d84984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6454 q = 1) (hb : d83662 q = 1) : d84985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6454, d84985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6454, d84985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6455 q = 1) (hb : d83662 q = 1) : d84986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6455, d84986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6455, d84986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1810 q = 1) (hb : d83662 q = 1) : d1810 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6457 q = 1) (hb : d83662 q = 1) : d84988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6457, d84988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9917 q ha hb
    | true =>
      simp only [d6457, d84988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6458 q = 1) (hb : d83662 q = 1) : d84989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6458, d84989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6458, d84989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6459 q = 1) (hb : d83662 q = 1) : d84990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6459, d84990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6459, d84990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6462 q = 1) (hb : d83662 q = 1) : d84992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d84992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9918 q ha hb
    | true =>
      simp only [d6462, d84992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9919 q ha hb
  have h27 (q : Pattern) (ha : d76988 q = 1) (hb : d83662 q = 1) : d84993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d84993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d76988, d84993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6466 q = 1) (hb : d83662 q = 1) : d7963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d7963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9906 q ha hb
    | true =>
      simp only [d6466, d7963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6467 q = 1) (hb : d83662 q = 1) : d7964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6467, d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d76989 q = 1) (hb : d83662 q = 1) : d84994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d84994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d76989, d84994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76990 q = 1) (hb : d83662 q = 1) : d84995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76990, d84995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76990, d84995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d76991 q = 1) (hb : d83662 q = 1) : d84996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76991, d84996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76991, d84996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d76992 q = 1) (hb : d83662 q = 1) : d84997 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76992, d84997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76992, d84997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro9921 (p : Pattern) (ha : d76999 p = 1) (hb : d83662 p = 1) : d85006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6462 q = 1) (hb : d83662 q = 1) : d84992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d84992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9918 q ha hb
    | true =>
      simp only [d6462, d84992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9919 q ha hb
  have h2 (q : Pattern) (ha : d76988 q = 1) (hb : d83662 q = 1) : d84993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76988, d84993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76988, d84993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6466 q = 1) (hb : d83662 q = 1) : d7963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d7963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9906 q ha hb
    | true =>
      simp only [d6466, d7963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6467 q = 1) (hb : d83662 q = 1) : d7964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6467, d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76989 q = 1) (hb : d83662 q = 1) : d84994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76989, d84994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76989, d84994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76997 q = 1) (hb : d83662 q = 1) : d85004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76997, d85004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76997, d85004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76998 q = 1) (hb : d83662 q = 1) : d85005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76998, d85005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76998, d85005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76999 q = 1) (hb : d83662 q = 1) : d85006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76999, d85006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76999, d85006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9922 (p : Pattern) (ha : d1894 p = 1) (hb : d77842 p = 1) : d7984 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1882 q = 1) : d1882 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1893 q = 1) (hb : d77842 q = 1) : d7983 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1893, d77842, d7983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1893, d77842, d7983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1894 q = 1) (hb : d77842 q = 1) : d7984 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1894, d7984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1894, d7984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9923 (p : Pattern) (ha : d6494 p = 1) (hb : d83662 p = 1) : d85015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d77842 q = 1) : d7985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d7985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9922 q ha hb
    | true =>
      simp only [d1895, d7985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d77842 q = 1) : d7986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d7986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d7986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6491 q = 1) (hb : d83662 q = 1) : d85012 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6491, d83662, d85012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6491, d83662, d85012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6492 q = 1) (hb : d83662 q = 1) : d85013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6492, d85013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6492, d85013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6493 q = 1) (hb : d83662 q = 1) : d85014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6493, d85014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6493, d85014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6494 q = 1) (hb : d83662 q = 1) : d85015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6494, d85015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6494, d85015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9924 (p : Pattern) (ha : d6507 p = 1) (hb : d77842 p = 1) : d7988 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1892 q = 1) : d1892 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6505 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6506 q = 1) (hb : d77842 q = 1) : d7987 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6506, d77842, d7987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6506, d77842, d7987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6507 q = 1) (hb : d77842 q = 1) : d7988 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6507, d7988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6507, d7988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9925 (p : Pattern) (ha : d6513 p = 1) (hb : d83662 p = 1) : d8013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6508 q = 1) (hb : d77842 q = 1) : d7989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9924 q ha hb
    | true =>
      simp only [d6508, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6509 q = 1) (hb : d77842 q = 1) : d7990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6509, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6509, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6510 q = 1) (hb : d83662 q = 1) : d8010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6510, d83662, d8010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6510, d83662, d8010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6511 q = 1) (hb : d83662 q = 1) : d8011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6511, d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6511, d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6512 q = 1) (hb : d83662 q = 1) : d8012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6512, d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6512, d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6513 q = 1) (hb : d83662 q = 1) : d8013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6513, d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6513, d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9926 (p : Pattern) (ha : d6524 p = 1) (hb : d83662 p = 1) : d8013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d77842 q = 1) : d7989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8283 q ha hb
    | true =>
      simp only [d1900, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d77842 q = 1) : d7990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6521 q = 1) (hb : d83662 q = 1) : d8010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6521, d83662, d8010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6521, d83662, d8010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6522 q = 1) (hb : d83662 q = 1) : d8011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6522, d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6522, d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6523 q = 1) (hb : d83662 q = 1) : d8012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6523, d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6523, d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6524 q = 1) (hb : d83662 q = 1) : d8013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6524, d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6524, d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9927 (p : Pattern) (ha : d77009 p = 1) (hb : d83662 p = 1) : d85021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6514 q = 1) (hb : d83662 q = 1) : d85016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6514, d85016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9923 q ha hb
    | true =>
      simp only [d6514, d85016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9925 q ha hb
  have h2 (q : Pattern) (ha : d77005 q = 1) (hb : d83662 q = 1) : d85017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77005, d85017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77005, d85017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6525 q = 1) (hb : d83662 q = 1) : d8014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d8014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9926 q ha hb
    | true =>
      simp only [d6525, d8014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6526 q = 1) (hb : d83662 q = 1) : d8015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, d8015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6526, d8015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77006 q = 1) (hb : d83662 q = 1) : d85018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77006, d85018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77006, d85018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77007 q = 1) (hb : d83662 q = 1) : d85019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77007, d85019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77007, d85019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77008 q = 1) (hb : d83662 q = 1) : d85020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77008, d85020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77008, d85020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77009 q = 1) (hb : d83662 q = 1) : d85021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77009, d85021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77009, d85021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9928 (p : Pattern) (ha : d77015 p = 1) (hb : d83662 p = 1) : d85027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6410 q = 1) (hb : d83662 q = 1) : d84949 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6410, d84949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6410, d84949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9905 q ha hb
  have h2 (q : Pattern) (ha : d6411 q = 1) (hb : d83662 q = 1) : d84950 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6411, d84950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6411, d84950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6419 q = 1) (hb : d83662 q = 1) : d84957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d84957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9905 q ha hb
    | true =>
      simp only [d6419, d84957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9907 q ha hb
  have h4 (q : Pattern) (ha : d6420 q = 1) (hb : d83662 q = 1) : d84958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d84958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6420, d84958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6421 q = 1) (hb : d83662 q = 1) : d84959 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6421, d84959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6421, d84959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76993 q = 1) (hb : d83662 q = 1) : d84998 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76993, d84998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9915 q ha hb
    | true =>
      simp only [d76993, d84998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9920 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d83662 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6479 q = 1) (hb : d83662 q = 1) : d85000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6479, d85000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9910 q ha hb
    | true =>
      simp only [d6479, d85000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76994 q = 1) (hb : d83662 q = 1) : d85001 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76994, d85001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76994, d85001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76995 q = 1) (hb : d83662 q = 1) : d85002 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76995, d85002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d76995, d85002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d76996 q = 1) (hb : d83662 q = 1) : d85003 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76996, d85003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76996, d85003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d77000 q = 1) (hb : d83662 q = 1) : d85007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77000, d85007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77000, d85007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9921 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d83662 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d77001 q = 1) (hb : d83662 q = 1) : d85008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77001, d85008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77001, d85008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77002 q = 1) (hb : d83662 q = 1) : d85009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77002, d85009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77002, d85009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77003 q = 1) (hb : d83662 q = 1) : d85010 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77003, d85010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77003, d85010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d77004 q = 1) (hb : d83662 q = 1) : d85011 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77004, d85011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77004, d85011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77010 q = 1) (hb : d83662 q = 1) : d85022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77010, d85022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77010, d85022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9927 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d83662 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d77011 q = 1) (hb : d83662 q = 1) : d85023 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77011, d85023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d77011, d85023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d77012 q = 1) (hb : d83662 q = 1) : d85024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77012, d85024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77012, d85024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77013 q = 1) (hb : d83662 q = 1) : d85025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77013, d85025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77013, d85025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77014 q = 1) (hb : d83662 q = 1) : d85026 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77014, d85026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d77014, d85026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d77015 q = 1) (hb : d83662 q = 1) : d85027 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77015, d85027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77015, d85027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro9929 (p : Pattern) (ha : d77021 p = 1) (hb : d83662 p = 1) : d85033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77016 q = 1) (hb : d83662 q = 1) : d85028 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77016, d85028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77016, d85028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9928 q ha hb
  have h2 (q : Pattern) (ha : d77017 q = 1) (hb : d83662 q = 1) : d85029 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77017, d85029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77017, d85029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77018 q = 1) (hb : d83662 q = 1) : d85030 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77018, d85030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77018, d85030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77019 q = 1) (hb : d83662 q = 1) : d85031 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77019, d85031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77019, d85031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77020 q = 1) (hb : d83662 q = 1) : d85032 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77020, d85032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77020, d85032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77021 q = 1) (hb : d83662 q = 1) : d85033 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77021, d85033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77021, d85033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9930 (p : Pattern) (ha : d6550 p = 1) (hb : d83662 p = 1) : d8096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6549 q = 1) (hb : d83662 q = 1) : d8095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6549, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6550 q = 1) (hb : d83662 q = 1) : d8096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6550, d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6550, d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9931 (p : Pattern) (ha : d6556 p = 1) (hb : d83662 p = 1) : d85043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d83662 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6551 q = 1) (hb : d83662 q = 1) : d85038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9930 q ha hb
    | true =>
      simp only [d6551, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6552 q = 1) (hb : d83662 q = 1) : d85039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6553 q = 1) (hb : d83662 q = 1) : d85040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6553, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6554 q = 1) (hb : d83662 q = 1) : d85041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6555 q = 1) (hb : d83662 q = 1) : d85042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6556 q = 1) (hb : d83662 q = 1) : d85043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, d85043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6556, d85043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9932 (p : Pattern) (ha : d6559 p = 1) (hb : d83662 p = 1) : d8117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6549 q = 1) (hb : d83662 q = 1) : d8095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6549, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6559 q = 1) (hb : d83662 q = 1) : d8117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6559, d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6559, d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9933 (p : Pattern) (ha : d6565 p = 1) (hb : d83662 p = 1) : d85051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d83662 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6551 q = 1) (hb : d83662 q = 1) : d85038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9930 q ha hb
    | true =>
      simp only [d6551, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6552 q = 1) (hb : d83662 q = 1) : d85039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6553 q = 1) (hb : d83662 q = 1) : d85040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6553, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6554 q = 1) (hb : d83662 q = 1) : d85041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6555 q = 1) (hb : d83662 q = 1) : d85042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d83662 q = 1) : d2116 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6560 q = 1) (hb : d83662 q = 1) : d85046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d85046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9932 q ha hb
    | true =>
      simp only [d6560, d85046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6561 q = 1) (hb : d83662 q = 1) : d85047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d85047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6561, d85047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6562 q = 1) (hb : d83662 q = 1) : d85048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d85048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6562, d85048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d6563 q = 1) (hb : d83662 q = 1) : d85049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d85049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d85049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6564 q = 1) (hb : d83662 q = 1) : d85050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d85050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d85050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6565 q = 1) (hb : d83662 q = 1) : d85051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, d85051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6565, d85051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9934 (p : Pattern) (ha : d5258 p = 1) (hb : d77842 p = 1) : d8037 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2089 q = 1) : d2089 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5256 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5257 q = 1) (hb : d77842 q = 1) : d8036 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5257, d77842, d8036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5257, d77842, d8036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5258 q = 1) (hb : d77842 q = 1) : d8037 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5258, d8037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5258, d8037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9935 (p : Pattern) (ha : d5264 p = 1) (hb : d83662 p = 1) : d8096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5259 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9934 q ha hb
    | true =>
      simp only [d5259, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5260 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5260, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5261 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5261, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5262 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5262, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5263 q = 1) (hb : d83662 q = 1) : d8095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5263, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5264 q = 1) (hb : d83662 q = 1) : d8096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5264, d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5264, d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9936 (p : Pattern) (ha : d6625 p = 1) (hb : d83662 p = 1) : d85094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d83662 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6620 q = 1) (hb : d83662 q = 1) : d85038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6620, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9935 q ha hb
    | true =>
      simp only [d6620, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6621 q = 1) (hb : d83662 q = 1) : d85039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6621, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6621, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6622 q = 1) (hb : d83662 q = 1) : d85040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6622, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6622, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6623 q = 1) (hb : d83662 q = 1) : d85041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6623, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6623, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6624 q = 1) (hb : d83662 q = 1) : d85042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6624, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6624, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d83662 q = 1) : d2309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6625 q = 1) (hb : d83662 q = 1) : d85094 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6625, d85094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6625, d85094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9937 (p : Pattern) (ha : d6570 p = 1) (hb : d83662 p = 1) : d85056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6569 q = 1) (hb : d83662 q = 1) : d85055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, d85055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6569, d85055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6570 q = 1) (hb : d83662 q = 1) : d85056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6570, d85056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6570, d85056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9938 (p : Pattern) (ha : d6577 p = 1) (hb : d83662 p = 1) : d85063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6575 q = 1) (hb : d83662 q = 1) : d85061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, d85061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6575, d85061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6576 q = 1) (hb : d83662 q = 1) : d85062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, d85062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6576, d85062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6577 q = 1) (hb : d83662 q = 1) : d85063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6577, d85063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6577, d85063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9939 (p : Pattern) (ha : d2155 p = 1) (hb : d77842 p = 1) : d8075 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2153 q = 1) : d2153 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2089 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2154 q = 1) (hb : d77842 q = 1) : d8074 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2154, d77842, d8074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2154, d77842, d8074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2155 q = 1) (hb : d77842 q = 1) : d8075 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2155, d8075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2155, d8075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9940 (p : Pattern) (ha : d6584 p = 1) (hb : d83662 p = 1) : d85070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2156 q = 1) (hb : d77842 q = 1) : d8076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d8076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9939 q ha hb
    | true =>
      simp only [d2156, d8076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2157 q = 1) (hb : d77842 q = 1) : d8077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d8077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2157, d8077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6581 q = 1) (hb : d83662 q = 1) : d85067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, d83662, d85067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6581, d83662, d85067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6582 q = 1) (hb : d83662 q = 1) : d85068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, d85068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6582, d85068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6583 q = 1) (hb : d83662 q = 1) : d85069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, d85069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6583, d85069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6584 q = 1) (hb : d83662 q = 1) : d85070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6584, d85070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6584, d85070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9941 (p : Pattern) (ha : d77030 p = 1) (hb : d83662 p = 1) : d85076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d83662 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6571 q = 1) (hb : d83662 q = 1) : d85057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d85057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9937 q ha hb
    | true =>
      simp only [d6571, d85057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6572 q = 1) (hb : d83662 q = 1) : d85058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d85058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d85058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6573 q = 1) (hb : d83662 q = 1) : d85059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d85059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6573, d85059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6574 q = 1) (hb : d83662 q = 1) : d85060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d85060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d85060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d83662 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6578 q = 1) (hb : d83662 q = 1) : d85064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d85064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9938 q ha hb
    | true =>
      simp only [d6578, d85064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6579 q = 1) (hb : d83662 q = 1) : d85065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d85065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d85065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6580 q = 1) (hb : d83662 q = 1) : d85066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d85066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6580, d85066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6585 q = 1) (hb : d83662 q = 1) : d85071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d85071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9940 q ha hb
    | true =>
      simp only [d6585, d85071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9935 q ha hb
  have h11 (q : Pattern) (ha : d77026 q = 1) (hb : d83662 q = 1) : d85072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d85072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77026, d85072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6592 q = 1) (hb : d83662 q = 1) : d8097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d8097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9930 q ha hb
    | true =>
      simp only [d6592, d8097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6593 q = 1) (hb : d83662 q = 1) : d8098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6593, d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d77027 q = 1) (hb : d83662 q = 1) : d85073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d85073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77027, d85073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77028 q = 1) (hb : d83662 q = 1) : d85074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d85074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77028, d85074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77029 q = 1) (hb : d83662 q = 1) : d85075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d85075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77029, d85075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77030 q = 1) (hb : d83662 q = 1) : d85076 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77030, d85076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77030, d85076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro9942 (p : Pattern) (ha : d6598 p = 1) (hb : d83662 p = 1) : d85077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6569 q = 1) (hb : d83662 q = 1) : d85055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, d85055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6569, d85055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6598 q = 1) (hb : d83662 q = 1) : d85077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6598, d85077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6598, d85077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9943 (p : Pattern) (ha : d6603 p = 1) (hb : d83662 p = 1) : d85082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6575 q = 1) (hb : d83662 q = 1) : d85061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, d85061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6575, d85061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6576 q = 1) (hb : d83662 q = 1) : d85062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, d85062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6576, d85062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6603 q = 1) (hb : d83662 q = 1) : d85082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6603, d85082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6603, d85082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro9944 (p : Pattern) (ha : d6607 p = 1) (hb : d83662 p = 1) : d85086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d77842 q = 1) : d8076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d8076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9939 q ha hb
    | true =>
      simp only [d2156, d8076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d77842 q = 1) : d8077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d8077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d8077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6581 q = 1) (hb : d83662 q = 1) : d85067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, d83662, d85067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6581, d83662, d85067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6582 q = 1) (hb : d83662 q = 1) : d85068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, d85068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6582, d85068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6583 q = 1) (hb : d83662 q = 1) : d85069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, d85069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6583, d85069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6607 q = 1) (hb : d83662 q = 1) : d85086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6607, d85086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6607, d85086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9945 (p : Pattern) (ha : d6608 p = 1) (hb : d83662 p = 1) : d8117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9934 q ha hb
    | true =>
      simp only [d5259, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5261 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5261, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5262 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5262, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5263 q = 1) (hb : d83662 q = 1) : d8095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5263, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6608 q = 1) (hb : d83662 q = 1) : d8117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6608, d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6608, d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9946 (p : Pattern) (ha : d77035 p = 1) (hb : d83662 p = 1) : d85092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d83662 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6571 q = 1) (hb : d83662 q = 1) : d85057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d85057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9937 q ha hb
    | true =>
      simp only [d6571, d85057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6572 q = 1) (hb : d83662 q = 1) : d85058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d85058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d85058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6573 q = 1) (hb : d83662 q = 1) : d85059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d85059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6573, d85059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6574 q = 1) (hb : d83662 q = 1) : d85060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d85060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d85060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d83662 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6578 q = 1) (hb : d83662 q = 1) : d85064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d85064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9938 q ha hb
    | true =>
      simp only [d6578, d85064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6579 q = 1) (hb : d83662 q = 1) : d85065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d85065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d85065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6580 q = 1) (hb : d83662 q = 1) : d85066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d85066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6580, d85066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6585 q = 1) (hb : d83662 q = 1) : d85071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d85071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9940 q ha hb
    | true =>
      simp only [d6585, d85071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9935 q ha hb
  have h11 (q : Pattern) (ha : d77026 q = 1) (hb : d83662 q = 1) : d85072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77026, d85072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77026, d85072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6592 q = 1) (hb : d83662 q = 1) : d8097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d8097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9930 q ha hb
    | true =>
      simp only [d6592, d8097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6593 q = 1) (hb : d83662 q = 1) : d8098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6593, d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d77027 q = 1) (hb : d83662 q = 1) : d85073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77027, d85073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77027, d85073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77028 q = 1) (hb : d83662 q = 1) : d85074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77028, d85074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77028, d85074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77029 q = 1) (hb : d83662 q = 1) : d85075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77029, d85075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77029, d85075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2282 q = 1) (hb : d83662 q = 1) : d2282 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d6599 q = 1) (hb : d83662 q = 1) : d85078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6599, d85078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9942 q ha hb
    | true =>
      simp only [d6599, d85078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d6600 q = 1) (hb : d83662 q = 1) : d85079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6600, d85079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6600, d85079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6601 q = 1) (hb : d83662 q = 1) : d85080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6601, d85080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d6601, d85080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d6602 q = 1) (hb : d83662 q = 1) : d85081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6602, d85081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6602, d85081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d2288 q = 1) (hb : d83662 q = 1) : d2288 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d6604 q = 1) (hb : d83662 q = 1) : d85083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6604, d85083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9943 q ha hb
    | true =>
      simp only [d6604, d85083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d6605 q = 1) (hb : d83662 q = 1) : d85084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6605, d85084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6605, d85084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d6606 q = 1) (hb : d83662 q = 1) : d85085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6606, d85085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d6606, d85085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6609 q = 1) (hb : d83662 q = 1) : d85087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d85087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9944 q ha hb
    | true =>
      simp only [d6609, d85087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9945 q ha hb
  have h27 (q : Pattern) (ha : d77031 q = 1) (hb : d83662 q = 1) : d85088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d85088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d77031, d85088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6613 q = 1) (hb : d83662 q = 1) : d8118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d8118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9932 q ha hb
    | true =>
      simp only [d6613, d8118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6614 q = 1) (hb : d83662 q = 1) : d8119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6614, d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d77032 q = 1) (hb : d83662 q = 1) : d85089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d85089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d77032, d85089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d77033 q = 1) (hb : d83662 q = 1) : d85090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77033, d85090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d77033, d85090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d77034 q = 1) (hb : d83662 q = 1) : d85091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77034, d85091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77034, d85091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d77035 q = 1) (hb : d83662 q = 1) : d85092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77035, d85092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77035, d85092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro9947 (p : Pattern) (ha : d77042 p = 1) (hb : d83662 p = 1) : d85101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6609 q = 1) (hb : d83662 q = 1) : d85087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d85087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9944 q ha hb
    | true =>
      simp only [d6609, d85087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9945 q ha hb
  have h2 (q : Pattern) (ha : d77031 q = 1) (hb : d83662 q = 1) : d85088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77031, d85088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77031, d85088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6613 q = 1) (hb : d83662 q = 1) : d8118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d8118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9932 q ha hb
    | true =>
      simp only [d6613, d8118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6614 q = 1) (hb : d83662 q = 1) : d8119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6614, d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77032 q = 1) (hb : d83662 q = 1) : d85089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77032, d85089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77032, d85089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77040 q = 1) (hb : d83662 q = 1) : d85099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77040, d85099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77040, d85099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77041 q = 1) (hb : d83662 q = 1) : d85100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77041, d85100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77041, d85100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77042 q = 1) (hb : d83662 q = 1) : d85101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77042, d85101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77042, d85101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9948 (p : Pattern) (ha : d2372 p = 1) (hb : d77842 p = 1) : d8139 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2360 q = 1) : d2360 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2370 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2371 q = 1) (hb : d77842 q = 1) : d8138 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2371, d77842, d8138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2371, d77842, d8138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2372 q = 1) (hb : d77842 q = 1) : d8139 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2372, d8139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2372, d8139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9949 (p : Pattern) (ha : d6641 p = 1) (hb : d83662 p = 1) : d85110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d77842 q = 1) : d8140 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d8140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9948 q ha hb
    | true =>
      simp only [d2373, d8140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d77842 q = 1) : d8141 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d8141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d8141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6638 q = 1) (hb : d83662 q = 1) : d85107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6638, d83662, d85107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6638, d83662, d85107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6639 q = 1) (hb : d83662 q = 1) : d85108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6639, d85108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6639, d85108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6640 q = 1) (hb : d83662 q = 1) : d85109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6640, d85109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6640, d85109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6641 q = 1) (hb : d83662 q = 1) : d85110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6641, d85110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6641, d85110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9950 (p : Pattern) (ha : d6654 p = 1) (hb : d77842 p = 1) : d8143 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2370 q = 1) : d2370 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6653 q = 1) (hb : d77842 q = 1) : d8142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6653, d77842, d8142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6653, d77842, d8142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6654 q = 1) (hb : d77842 q = 1) : d8143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6654, d8143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6654, d8143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro9951 (p : Pattern) (ha : d6660 p = 1) (hb : d83662 p = 1) : d8168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6655 q = 1) (hb : d77842 q = 1) : d8144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6655, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9950 q ha hb
    | true =>
      simp only [d6655, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6656 q = 1) (hb : d77842 q = 1) : d8145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6656, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6657 q = 1) (hb : d83662 q = 1) : d8165 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6657, d83662, d8165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6657, d83662, d8165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6658 q = 1) (hb : d83662 q = 1) : d8166 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6658, d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6658, d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6659 q = 1) (hb : d83662 q = 1) : d8167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6659, d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6659, d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6660 q = 1) (hb : d83662 q = 1) : d8168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6660, d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6660, d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9952 (p : Pattern) (ha : d6671 p = 1) (hb : d83662 p = 1) : d8168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d77842 q = 1) : d8144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8311 q ha hb
    | true =>
      simp only [d2378, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d77842 q = 1) : d8145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6668 q = 1) (hb : d83662 q = 1) : d8165 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6668, d83662, d8165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6668, d83662, d8165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6669 q = 1) (hb : d83662 q = 1) : d8166 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6669, d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6669, d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6670 q = 1) (hb : d83662 q = 1) : d8167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6670, d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6670, d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6671 q = 1) (hb : d83662 q = 1) : d8168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6671, d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6671, d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9953 (p : Pattern) (ha : d77052 p = 1) (hb : d83662 p = 1) : d85116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6661 q = 1) (hb : d83662 q = 1) : d85111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6661, d85111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9949 q ha hb
    | true =>
      simp only [d6661, d85111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9951 q ha hb
  have h2 (q : Pattern) (ha : d77048 q = 1) (hb : d83662 q = 1) : d85112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77048, d85112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77048, d85112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6672 q = 1) (hb : d83662 q = 1) : d8169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d8169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9952 q ha hb
    | true =>
      simp only [d6672, d8169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6673 q = 1) (hb : d83662 q = 1) : d8170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d8170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6673, d8170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77049 q = 1) (hb : d83662 q = 1) : d85113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77049, d85113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77049, d85113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77050 q = 1) (hb : d83662 q = 1) : d85114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77050, d85114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77050, d85114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77051 q = 1) (hb : d83662 q = 1) : d85115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77051, d85115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77051, d85115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77052 q = 1) (hb : d83662 q = 1) : d85116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77052, d85116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77052, d85116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9954 (p : Pattern) (ha : d77058 p = 1) (hb : d83662 p = 1) : d85122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6557 q = 1) (hb : d83662 q = 1) : d85044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6557, d85044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6557, d85044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9931 q ha hb
  have h2 (q : Pattern) (ha : d6558 q = 1) (hb : d83662 q = 1) : d85045 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6558, d85045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6558, d85045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6566 q = 1) (hb : d83662 q = 1) : d85052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d85052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9931 q ha hb
    | true =>
      simp only [d6566, d85052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9933 q ha hb
  have h4 (q : Pattern) (ha : d6567 q = 1) (hb : d83662 q = 1) : d85053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d85053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6567, d85053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6568 q = 1) (hb : d83662 q = 1) : d85054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6568, d85054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6568, d85054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77036 q = 1) (hb : d83662 q = 1) : d85093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77036, d85093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9941 q ha hb
    | true =>
      simp only [d77036, d85093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9946 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d83662 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6626 q = 1) (hb : d83662 q = 1) : d85095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6626, d85095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9936 q ha hb
    | true =>
      simp only [d6626, d85095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77037 q = 1) (hb : d83662 q = 1) : d85096 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77037, d85096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77037, d85096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77038 q = 1) (hb : d83662 q = 1) : d85097 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77038, d85097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77038, d85097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d77039 q = 1) (hb : d83662 q = 1) : d85098 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77039, d85098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77039, d85098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d77043 q = 1) (hb : d83662 q = 1) : d85102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77043, d85102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77043, d85102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9947 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d83662 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d77044 q = 1) (hb : d83662 q = 1) : d85103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77044, d85103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77044, d85103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77045 q = 1) (hb : d83662 q = 1) : d85104 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77045, d85104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77045, d85104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77046 q = 1) (hb : d83662 q = 1) : d85105 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77046, d85105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77046, d85105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d77047 q = 1) (hb : d83662 q = 1) : d85106 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77047, d85106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77047, d85106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77053 q = 1) (hb : d83662 q = 1) : d85117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77053, d85117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77053, d85117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9953 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d83662 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d77054 q = 1) (hb : d83662 q = 1) : d85118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77054, d85118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d77054, d85118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d77055 q = 1) (hb : d83662 q = 1) : d85119 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77055, d85119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77055, d85119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77056 q = 1) (hb : d83662 q = 1) : d85120 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77056, d85120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77056, d85120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77057 q = 1) (hb : d83662 q = 1) : d85121 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77057, d85121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d77057, d85121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d77058 q = 1) (hb : d83662 q = 1) : d85122 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77058, d85122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77058, d85122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro9955 (p : Pattern) (ha : d77064 p = 1) (hb : d83662 p = 1) : d85128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77059 q = 1) (hb : d83662 q = 1) : d85123 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77059, d85123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77059, d85123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9954 q ha hb
  have h2 (q : Pattern) (ha : d77060 q = 1) (hb : d83662 q = 1) : d85124 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77060, d85124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77060, d85124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77061 q = 1) (hb : d83662 q = 1) : d85125 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77061, d85125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77061, d85125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77062 q = 1) (hb : d83662 q = 1) : d85126 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77062, d85126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77062, d85126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77063 q = 1) (hb : d83662 q = 1) : d85127 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77063, d85127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77063, d85127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77064 q = 1) (hb : d83662 q = 1) : d85128 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77064, d85128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77064, d85128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9956 (p : Pattern) (ha : d77070 p = 1) (hb : d83662 p = 1) : d85134 p = 1 := by
  have h0 (q : Pattern) (ha : d76899 q = 1) (hb : d83662 q = 1) : d84755 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76899, d84755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9825 q ha hb
    | true =>
      simp only [d76899, d84755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9851 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76939 q = 1) (hb : d83662 q = 1) : d84847 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76939, d84847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76939, d84847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9877 q ha hb
  have h3 (q : Pattern) (ha : d76940 q = 1) (hb : d83662 q = 1) : d84848 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76940, d84848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76940, d84848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76980 q = 1) (hb : d83662 q = 1) : d84940 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76980, d84940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76980, d84940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9903 q ha hb
  have h5 (q : Pattern) (ha : d76981 q = 1) (hb : d83662 q = 1) : d84941 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76981, d84941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76981, d84941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76982 q = 1) (hb : d83662 q = 1) : d84942 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76982, d84942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76982, d84942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77022 q = 1) (hb : d83662 q = 1) : d85034 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77022, d85034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77022, d85034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9929 q ha hb
  have h8 (q : Pattern) (ha : d77023 q = 1) (hb : d83662 q = 1) : d85035 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77023, d85035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77023, d85035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77024 q = 1) (hb : d83662 q = 1) : d85036 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77024, d85036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77024, d85036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77025 q = 1) (hb : d83662 q = 1) : d85037 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77025, d85037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77025, d85037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77065 q = 1) (hb : d83662 q = 1) : d85129 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77065, d85129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77065, d85129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9955 q ha hb
  have h12 (q : Pattern) (ha : d77066 q = 1) (hb : d83662 q = 1) : d85130 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77066, d85130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77066, d85130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77067 q = 1) (hb : d83662 q = 1) : d85131 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77067, d85131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77067, d85131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77068 q = 1) (hb : d83662 q = 1) : d85132 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77068, d85132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77068, d85132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77069 q = 1) (hb : d83662 q = 1) : d85133 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77069, d85133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77069, d85133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77070 q = 1) (hb : d83662 q = 1) : d85134 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77070, d85134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77070, d85134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro9957 (p : Pattern) (ha : d77076 p = 1) (hb : d83662 p = 1) : d85140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77071 q = 1) (hb : d83662 q = 1) : d85135 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77071, d85135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9956 q ha hb
    | true =>
      simp only [d77071, d85135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77072 q = 1) (hb : d83662 q = 1) : d85136 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77072, d85136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77072, d85136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77073 q = 1) (hb : d83662 q = 1) : d85137 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77073, d85137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77073, d85137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77074 q = 1) (hb : d83662 q = 1) : d85138 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77074, d85138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77074, d85138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77075 q = 1) (hb : d83662 q = 1) : d85139 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77075, d85139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77075, d85139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77076 q = 1) (hb : d83662 q = 1) : d85140 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77076, d85140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77076, d85140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9958 (p : Pattern) (ha : d77082 p = 1) (hb : d83662 p = 1) : d85146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77077 q = 1) (hb : d83662 q = 1) : d85141 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77077, d85141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9957 q ha hb
    | true =>
      simp only [d77077, d85141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77078 q = 1) (hb : d83662 q = 1) : d85142 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77078, d85142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77078, d85142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77079 q = 1) (hb : d83662 q = 1) : d85143 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77079, d85143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77079, d85143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77080 q = 1) (hb : d83662 q = 1) : d85144 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77080, d85144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77080, d85144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77081 q = 1) (hb : d83662 q = 1) : d85145 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77081, d85145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77081, d85145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77082 q = 1) (hb : d83662 q = 1) : d85146 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77082, d85146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77082, d85146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9959 (p : Pattern) (ha : d77088 p = 1) (hb : d83662 p = 1) : d85152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77083 q = 1) (hb : d83662 q = 1) : d85147 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77083, d85147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9958 q ha hb
    | true =>
      simp only [d77083, d85147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77084 q = 1) (hb : d83662 q = 1) : d85148 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77084, d85148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77084, d85148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77085 q = 1) (hb : d83662 q = 1) : d85149 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77085, d85149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77085, d85149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77086 q = 1) (hb : d83662 q = 1) : d85150 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77086, d85150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77086, d85150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77087 q = 1) (hb : d83662 q = 1) : d85151 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77087, d85151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77087, d85151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77088 q = 1) (hb : d83662 q = 1) : d85152 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77088, d85152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77088, d85152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9960 (p : Pattern) (ha : d77094 p = 1) (hb : d83662 p = 1) : d85158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77089 q = 1) (hb : d83662 q = 1) : d85153 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77089, d85153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9959 q ha hb
    | true =>
      simp only [d77089, d85153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77090 q = 1) (hb : d83662 q = 1) : d85154 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77090, d85154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77090, d85154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77091 q = 1) (hb : d83662 q = 1) : d85155 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77091, d85155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77091, d85155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77092 q = 1) (hb : d83662 q = 1) : d85156 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77092, d85156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77092, d85156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77093 q = 1) (hb : d83662 q = 1) : d85157 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77093, d85157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77093, d85157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77094 q = 1) (hb : d83662 q = 1) : d85158 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77094, d85158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77094, d85158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9961 (p : Pattern) (ha : d77100 p = 1) (hb : d83662 p = 1) : d85164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77095 q = 1) (hb : d83662 q = 1) : d85159 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77095, d85159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9960 q ha hb
    | true =>
      simp only [d77095, d85159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77096 q = 1) (hb : d83662 q = 1) : d85160 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77096, d85160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77096, d85160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77097 q = 1) (hb : d83662 q = 1) : d85161 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77097, d85161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77097, d85161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77098 q = 1) (hb : d83662 q = 1) : d85162 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77098, d85162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77098, d85162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77099 q = 1) (hb : d83662 q = 1) : d85163 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77099, d85163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77099, d85163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77100 q = 1) (hb : d83662 q = 1) : d85164 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77100, d85164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77100, d85164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9962 (p : Pattern) (ha : d77106 p = 1) (hb : d83662 p = 1) : d85170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77101 q = 1) (hb : d83662 q = 1) : d85165 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77101, d85165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9961 q ha hb
    | true =>
      simp only [d77101, d85165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77102 q = 1) (hb : d83662 q = 1) : d85166 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77102, d85166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77102, d85166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77103 q = 1) (hb : d83662 q = 1) : d85167 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77103, d85167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77103, d85167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77104 q = 1) (hb : d83662 q = 1) : d85168 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77104, d85168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77104, d85168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77105 q = 1) (hb : d83662 q = 1) : d85169 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77105, d85169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77105, d85169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77106 q = 1) (hb : d83662 q = 1) : d85170 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77106, d85170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77106, d85170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9963 (p : Pattern) (ha : d77112 p = 1) (hb : d83662 p = 1) : d85176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77107 q = 1) (hb : d83662 q = 1) : d85171 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77107, d85171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9962 q ha hb
    | true =>
      simp only [d77107, d85171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77108 q = 1) (hb : d83662 q = 1) : d85172 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77108, d85172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77108, d85172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77109 q = 1) (hb : d83662 q = 1) : d85173 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77109, d85173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77109, d85173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77110 q = 1) (hb : d83662 q = 1) : d85174 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77110, d85174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77110, d85174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77111 q = 1) (hb : d83662 q = 1) : d85175 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77111, d85175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77111, d85175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77112 q = 1) (hb : d83662 q = 1) : d85176 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77112, d85176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77112, d85176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9964 (p : Pattern) (ha : d7241 p = 1) (hb : d83664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7240 q = 1) (hb : d83663 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7240, d83663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7240, d83663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7241 q = 1) (hb : d83664 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7241, d83664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7241, d83664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro9965 (p : Pattern) (ha : d7347 p = 1) (hb : d83670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7345 q = 1) (hb : d83668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7345, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7346 q = 1) (hb : d83669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d83669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7346, d83669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7347 q = 1) (hb : d83670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, d83670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7347, d83670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9966 (p : Pattern) (ha : d83676 p = 1) (hb : d84548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83671 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9965 q hb ha
    | true =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d84544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83672, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d84545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d84546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d84547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83676 q = 1) (hb : d84548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83676, d84548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83676, d84548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro9967 (p : Pattern) (ha : d7368 p = 1) (hb : d83677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7345 q = 1) (hb : d83668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7345, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7346 q = 1) (hb : d83669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d83669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7346, d83669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7368 q = 1) (hb : d83677 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, d83677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7368, d83677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9968 (p : Pattern) (ha : d83683 p = 1) (hb : d84554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83671 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9965 q hb ha
    | true =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d84544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83672, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d84545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d84546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d84547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d83678 q = 1) (hb : d84549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9967 q hb ha
    | true =>
      simp only [d83678, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83679 q = 1) (hb : d84550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83679, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d83680 q = 1) (hb : d84551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83680, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83681 q = 1) (hb : d84552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83681, d84552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d83681, d84552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83682 q = 1) (hb : d84553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83682, d84553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d83682, d84553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83683 q = 1) (hb : d84554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83683, d84554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83683, d84554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro9969 (p : Pattern) (ha : d83690 p = 1) (hb : d84561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83678 q = 1) (hb : d84549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9967 q hb ha
    | true =>
      simp only [d83678, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83679 q = 1) (hb : d84550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83679, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83680 q = 1) (hb : d84551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83680, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83688 q = 1) (hb : d84559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83688, d84559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83688, d84559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83689 q = 1) (hb : d84560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83689, d84560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83689, d84560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83690 q = 1) (hb : d84561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83690, d84561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83690, d84561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9970 (p : Pattern) (ha : d7274 p = 1) (hb : d83697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7273 q = 1) (hb : d83696 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7273, d83696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7273, d83696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7274 q = 1) (hb : d83697 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7274, d83697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7274, d83697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro9971 (p : Pattern) (ha : d7411 p = 1) (hb : d83703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d83698 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9970 q ha hb
    | true =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d83699 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7408 q = 1) (hb : d83700 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d83700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7408, d83700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7409 q = 1) (hb : d83701 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, d83701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7409, d83701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7410 q = 1) (hb : d83702 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, d83702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7410, d83702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7411 q = 1) (hb : d83703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, d83703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7411, d83703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9972 (p : Pattern) (ha : d83709 p = 1) (hb : d84572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83704 q = 1) (hb : d84567 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83704, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9971 q hb ha
    | true =>
      simp only [d83704, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83705 q = 1) (hb : d84568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83705, d84568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83705, d84568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83706 q = 1) (hb : d84569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83706, d84569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83706, d84569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83707 q = 1) (hb : d84570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83707, d84570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83707, d84570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83708 q = 1) (hb : d84571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83708, d84571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83708, d84571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83709 q = 1) (hb : d84572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83709, d84572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83709, d84572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9973 (p : Pattern) (ha : d83715 p = 1) (hb : d84578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83684 q = 1) (hb : d84555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83684, d84555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9966 q ha hb
    | true =>
      simp only [d83684, d84555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9968 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83685 q = 1) (hb : d84556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83685, d84556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83685, d84556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d83686 q = 1) (hb : d84557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83686, d84557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83686, d84557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83687 q = 1) (hb : d84558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83687, d84558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83687, d84558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83691 q = 1) (hb : d84562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83691, d84562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83691, d84562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9969 q ha hb
  have h12 (q : Pattern) (ha : d83692 q = 1) (hb : d84563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83692, d84563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83692, d84563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83693 q = 1) (hb : d84564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83693, d84564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83693, d84564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83694 q = 1) (hb : d84565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83694, d84565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83694, d84565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83695 q = 1) (hb : d84566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83695, d84566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83695, d84566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83710 q = 1) (hb : d84573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83710, d84573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83710, d84573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9972 q ha hb
  have h17 (q : Pattern) (ha : d83711 q = 1) (hb : d84574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83711, d84574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83711, d84574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d83712 q = 1) (hb : d84575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83712, d84575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83712, d84575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83713 q = 1) (hb : d84576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83713, d84576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d83713, d84576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d83714 q = 1) (hb : d84577 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83714, d84577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83714, d84577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83715 q = 1) (hb : d84578 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83715, d84578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83715, d84578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro9974 (p : Pattern) (ha : d83725 p = 1) (hb : d84588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9965 q hb ha
    | true =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d84584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d84585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d84586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d84587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83725 q = 1) (hb : d84588 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83725, d84588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83725, d84588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9975 (p : Pattern) (ha : d83732 p = 1) (hb : d84595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9965 q hb ha
    | true =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d84584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d84585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d84586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d84587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83678 q = 1) (hb : d84549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9967 q hb ha
    | true =>
      simp only [d83678, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d83728 q = 1) (hb : d84591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83728, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83728, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83729 q = 1) (hb : d84592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83729, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83729, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83730 q = 1) (hb : d84593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83730, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83730, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83731 q = 1) (hb : d84594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83731, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83731, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83732 q = 1) (hb : d84595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83732, d84595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83732, d84595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro9976 (p : Pattern) (ha : d7347 p = 1) (hb : d83761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d83758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d83758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d83759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d83759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d83759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d83760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d83760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d83760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7347 q = 1) (hb : d83761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, d83761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7347, d83761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9977 (p : Pattern) (ha : d7326 p = 1) (hb : d83749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d328 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d328, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7325 q = 1) (hb : d83748 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, d83748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7325, d83748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7326 q = 1) (hb : d83749 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, d83749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7326, d83749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro9978 (p : Pattern) (ha : d7486 p = 1) (hb : d83755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d83752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d83752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d83752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d83753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d83753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d83753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7485 q = 1) (hb : d83754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d83754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7485, d83754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7486 q = 1) (hb : d83755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d83755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d83755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9979 (p : Pattern) (ha : d83737 p = 1) (hb : d84600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7345 q = 1) (hb : d83668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7345, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83736 q = 1) (hb : d84599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83736, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83736, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83737 q = 1) (hb : d84600 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83737, d84600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83737, d84600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9980 (p : Pattern) (ha : d83744 p = 1) (hb : d84607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83742 q = 1) (hb : d84605 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83742, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83742, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83743 q = 1) (hb : d84606 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83743, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83743, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83744 q = 1) (hb : d84607 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83744, d84607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83744, d84607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9981 (p : Pattern) (ha : d83767 p = 1) (hb : d84616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83738 q = 1) (hb : d84601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83738, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9979 q ha hb
    | true =>
      simp only [d83738, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d83739 q = 1) (hb : d84602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83739, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83739, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83740 q = 1) (hb : d84603 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83740, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83740, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83741 q = 1) (hb : d84604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83741, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83741, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83745 q = 1) (hb : d84608 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83745, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9980 q ha hb
    | true =>
      simp only [d83745, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d83746 q = 1) (hb : d84609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83746, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83746, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83747 q = 1) (hb : d84610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83747, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83747, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d84611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9978 q hb ha
    | true =>
      simp only [d83756, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9965 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d84612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7348 q = 1) (hb : d83762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9976 q ha hb
    | true =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d84613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d84614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83765, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d84615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83766, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83767 q = 1) (hb : d84616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83767, d84616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83767, d84616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro9982 (p : Pattern) (ha : d7368 p = 1) (hb : d83780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d83758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d83758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d83759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d83759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d83759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d83760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d83760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d83760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7368 q = 1) (hb : d83780 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, d83780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7368, d83780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9983 (p : Pattern) (ha : d7507 p = 1) (hb : d83777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d83752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d83752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d83752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d83753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d83753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d83753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7485 q = 1) (hb : d83754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d83754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7485, d83754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7507 q = 1) (hb : d83777 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d83777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7507, d83777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9984 (p : Pattern) (ha : d83768 p = 1) (hb : d84617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7345 q = 1) (hb : d83668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7345, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83736 q = 1) (hb : d84599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83736, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83736, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83768 q = 1) (hb : d84617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83768, d84617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83768, d84617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro9985 (p : Pattern) (ha : d83773 p = 1) (hb : d84622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7344 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83742 q = 1) (hb : d84605 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83742, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83742, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83743 q = 1) (hb : d84606 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83743, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83743, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83773 q = 1) (hb : d84622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83773, d84622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83773, d84622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro9986 (p : Pattern) (ha : d83786 p = 1) (hb : d84631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83738 q = 1) (hb : d84601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83738, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9979 q ha hb
    | true =>
      simp only [d83738, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d83739 q = 1) (hb : d84602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83739, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83739, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83740 q = 1) (hb : d84603 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83740, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83740, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83741 q = 1) (hb : d84604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83741, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83741, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83745 q = 1) (hb : d84608 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83745, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9980 q ha hb
    | true =>
      simp only [d83745, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d83746 q = 1) (hb : d84609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83746, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83746, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83747 q = 1) (hb : d84610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83747, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83747, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d84611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9978 q hb ha
    | true =>
      simp only [d83756, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9965 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d84612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7348 q = 1) (hb : d83762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9976 q ha hb
    | true =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d84613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d84614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83765, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d84615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83766, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83769 q = 1) (hb : d84618 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83769, d84618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9984 q ha hb
    | true =>
      simp only [d83769, d84618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d83770 q = 1) (hb : d84619 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83770, d84619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83770, d84619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83771 q = 1) (hb : d84620 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83771, d84620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83771, d84620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83772 q = 1) (hb : d84621 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83772, d84621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83772, d84621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d83774 q = 1) (hb : d84623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83774, d84623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9985 q ha hb
    | true =>
      simp only [d83774, d84623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d83775 q = 1) (hb : d84624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83775, d84624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83775, d84624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d83776 q = 1) (hb : d84625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83776, d84625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83776, d84625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83778 q = 1) (hb : d84626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9983 q hb ha
    | true =>
      simp only [d83778, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9967 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83779 q = 1) (hb : d84627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83779, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7369 q = 1) (hb : d83781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9982 q ha hb
    | true =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7370 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d83783 q = 1) (hb : d84628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83783, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83784 q = 1) (hb : d84629 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83784, d84629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d83784, d84629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83785 q = 1) (hb : d84630 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83785, d84630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83785, d84630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83786 q = 1) (hb : d84631 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83786, d84631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83786, d84631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro9987 (p : Pattern) (ha : d83788 p = 1) (hb : d84633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83671 q = 1) (hb : d84543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9965 q hb ha
    | true =>
      simp only [d83671, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d83721 q = 1) (hb : d84584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83721, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83721, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83722 q = 1) (hb : d84585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83722, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83722, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83723 q = 1) (hb : d84586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83723, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83723, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83724 q = 1) (hb : d84587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83724, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83724, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83788 q = 1) (hb : d84633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83788, d84633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83788, d84633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro9988 (p : Pattern) (ha : d83795 p = 1) (hb : d84640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83778 q = 1) (hb : d84626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9983 q hb ha
    | true =>
      simp only [d83778, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9967 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83779 q = 1) (hb : d84627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83779, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7369 q = 1) (hb : d83781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9982 q ha hb
    | true =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7370 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83783 q = 1) (hb : d84628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83783, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83793 q = 1) (hb : d84638 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83793, d84638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83793, d84638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83794 q = 1) (hb : d84639 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83794, d84639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83794, d84639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83795 q = 1) (hb : d84640 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d84640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d84640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9989 (p : Pattern) (ha : d7411 p = 1) (hb : d83814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d83698 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9970 q ha hb
    | true =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d83699 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7408 q = 1) (hb : d83811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d83811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7408, d83811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7409 q = 1) (hb : d83812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, d83812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7409, d83812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7410 q = 1) (hb : d83813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, d83813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7410, d83813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7411 q = 1) (hb : d83814 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, d83814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7411, d83814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9990 (p : Pattern) (ha : d7390 p = 1) (hb : d83802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d421 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d421, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7389 q = 1) (hb : d83801 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, d83801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7389, d83801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7390 q = 1) (hb : d83802 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, d83802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7390, d83802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro9991 (p : Pattern) (ha : d7554 p = 1) (hb : d83808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d83803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9990 q ha hb
    | true =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d83804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83699 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7551 q = 1) (hb : d83805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d83805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7551, d83805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7552 q = 1) (hb : d83806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, d83806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7552, d83806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7553 q = 1) (hb : d83807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, d83807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7553, d83807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7554 q = 1) (hb : d83808 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, d83808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7554, d83808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9992 (p : Pattern) (ha : d83820 p = 1) (hb : d84651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83809 q = 1) (hb : d84646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83809, d84646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9991 q hb ha
    | true =>
      simp only [d83809, d84646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9971 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d84647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d84647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83810, d84647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7412 q = 1) (hb : d83815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d83815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9989 q ha hb
    | true =>
      simp only [d7412, d83815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7413 q = 1) (hb : d83816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, d83816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7413, d83816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83817 q = 1) (hb : d84648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d84648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d84648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83818 q = 1) (hb : d84649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d84649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d84649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83819 q = 1) (hb : d84650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d84650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d84650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83820 q = 1) (hb : d84651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d84651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d84651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9993 (p : Pattern) (ha : d83826 p = 1) (hb : d84657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83726 q = 1) (hb : d84589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83726, d84589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83726, d84589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9974 q ha hb
  have h2 (q : Pattern) (ha : d83727 q = 1) (hb : d84590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83727, d84590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83727, d84590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83733 q = 1) (hb : d84596 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83733, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9974 q ha hb
    | true =>
      simp only [d83733, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9975 q ha hb
  have h4 (q : Pattern) (ha : d83734 q = 1) (hb : d84597 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83734, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83734, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83735 q = 1) (hb : d84598 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83735, d84598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83735, d84598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83787 q = 1) (hb : d84632 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83787, d84632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9981 q ha hb
    | true =>
      simp only [d83787, d84632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9986 q ha hb
  have h7 (q : Pattern) (ha : d83789 q = 1) (hb : d84634 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83789, d84634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9987 q ha hb
    | true =>
      simp only [d83789, d84634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d83790 q = 1) (hb : d84635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83790, d84635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83790, d84635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83791 q = 1) (hb : d84636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d84636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83791, d84636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83792 q = 1) (hb : d84637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d84637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83792, d84637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83796 q = 1) (hb : d84641 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d84641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83796, d84641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9988 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d83797 q = 1) (hb : d84642 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d84642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83797, d84642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83798 q = 1) (hb : d84643 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d84643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83798, d84643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83799 q = 1) (hb : d84644 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d84644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83799, d84644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83800 q = 1) (hb : d84645 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d84645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83800, d84645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83821 q = 1) (hb : d84652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d84652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83821, d84652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9992 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d83822 q = 1) (hb : d84653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d84653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83822, d84653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83823 q = 1) (hb : d84654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d84654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83823, d84654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83824 q = 1) (hb : d84655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d84655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83824, d84655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83825 q = 1) (hb : d84656 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d84656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83825, d84656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83826 q = 1) (hb : d84657 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d84657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83826, d84657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro9994 (p : Pattern) (ha : d83832 p = 1) (hb : d84663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83716 q = 1) (hb : d84579 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83716, d84579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83716, d84579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9973 q ha hb
  have h6 (q : Pattern) (ha : d83717 q = 1) (hb : d84580 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83717, d84580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83717, d84580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83718 q = 1) (hb : d84581 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83718, d84581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83718, d84581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83719 q = 1) (hb : d84582 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83719, d84582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83719, d84582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83720 q = 1) (hb : d84583 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83720, d84583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83720, d84583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83827 q = 1) (hb : d84658 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d84658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83827, d84658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9993 q ha hb
  have h11 (q : Pattern) (ha : d83828 q = 1) (hb : d84659 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d84659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83828, d84659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83829 q = 1) (hb : d84660 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d84660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83829, d84660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83830 q = 1) (hb : d84661 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d84661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83830, d84661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83831 q = 1) (hb : d84662 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d84662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83831, d84662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83832 q = 1) (hb : d84663 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d84663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83832, d84663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro9995 (p : Pattern) (ha : d7486 p = 1) (hb : d83836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d83833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d83834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7485 q = 1) (hb : d83835 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d83835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7485, d83835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7486 q = 1) (hb : d83836 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d83836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d83836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9996 (p : Pattern) (ha : d83842 p = 1) (hb : d84669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d84664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9995 q hb ha
    | true =>
      simp only [d83837, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d84665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d84666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d84667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d84668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83842 q = 1) (hb : d84669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83842, d84669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83842, d84669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9997 (p : Pattern) (ha : d7507 p = 1) (hb : d83845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7483 q = 1) (hb : d83833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7484 q = 1) (hb : d83834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7484, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7485 q = 1) (hb : d83835 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d83835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7485, d83835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7507 q = 1) (hb : d83845 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d83845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7507, d83845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9998 (p : Pattern) (ha : d83851 p = 1) (hb : d84677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83837 q = 1) (hb : d84664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9995 q hb ha
    | true =>
      simp only [d83837, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h2 (q : Pattern) (ha : d83838 q = 1) (hb : d84665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83838, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83838, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83839 q = 1) (hb : d84666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83839, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83839, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83840 q = 1) (hb : d84667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83840, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83840, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83841 q = 1) (hb : d84668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83841, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83841, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83846 q = 1) (hb : d84672 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9997 q hb ha
    | true =>
      simp only [d83846, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h7 (q : Pattern) (ha : d83847 q = 1) (hb : d84673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83847, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83847, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83848 q = 1) (hb : d84674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83848, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83848, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83849 q = 1) (hb : d84675 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83849, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83849, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83850 q = 1) (hb : d84676 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83850, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83850, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83851 q = 1) (hb : d84677 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83851, d84677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83851, d84677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro9999 (p : Pattern) (ha : d7486 p = 1) (hb : d83880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d83877 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d83877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d83877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d83878 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d83878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d83878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d83879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d83879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d83879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7486 q = 1) (hb : d83880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d83880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d83880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
