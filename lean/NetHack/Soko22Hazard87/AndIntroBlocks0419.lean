import NetHack.Soko22Hazard87.AndIntroBlocks0418
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro104750 (p : Pattern) (ha : d46025 p = 1) (hb : d271212 p = 1) : d369919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d271212 q = 1) : d369876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104732 q ha hb
    | true =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d271212 q = 1) : d369877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d271212 q = 1) : d369880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104733 q ha hb
    | true =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d271212 q = 1) : d369881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d271212 q = 1) : d369882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d369882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d369882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46023 q = 1) (hb : d271212 q = 1) : d369917 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46023, d369917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46023, d369917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46024 q = 1) (hb : d271212 q = 1) : d369918 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46024, d369918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46024, d369918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46025 q = 1) (hb : d271212 q = 1) : d369919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46025, d369919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46025, d369919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104751 (p : Pattern) (ha : d46028 p = 1) (hb : d271212 p = 1) : d369922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d271212 q = 1) : d369880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104733 q ha hb
    | true =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d271212 q = 1) : d369881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d271212 q = 1) : d369886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d369886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d369886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46026 q = 1) (hb : d271212 q = 1) : d369920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46026, d369920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46026, d369920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46027 q = 1) (hb : d271212 q = 1) : d369921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46027, d369921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46027, d369921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46028 q = 1) (hb : d271212 q = 1) : d369922 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46028, d369922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46028, d369922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104752 (p : Pattern) (ha : d46035 p = 1) (hb : d271212 p = 1) : d369926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45571 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104692 q ha hb
    | true =>
      simp only [d45571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d45572 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45572, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46032 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46033 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46034 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45905 q = 1) (hb : d271211 q = 1) : d46042 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d46042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104639 q ha hb
    | true =>
      simp only [d45905, d46042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68906 q ha hb
  have h9 (q : Pattern) (ha : d45906 q = 1) (hb : d271212 q = 1) : d46043 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d271212, d46043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45906, d271212, d46043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d45907 q = 1) (hb : d271212 q = 1) : d46053 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45907, d46053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45907, d46053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45574 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104693 q ha hb
    | true =>
      simp only [d45574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d45575 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45575, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d45576 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45908 q = 1) (hb : d271212 q = 1) : d46054 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45908, d46054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45908, d46054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45909 q = 1) (hb : d271212 q = 1) : d46055 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45909, d46055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45909, d46055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d46035 q = 1) (hb : d271212 q = 1) : d369926 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46035, d369926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46035, d369926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104753 (p : Pattern) (ha : d46047 p = 1) (hb : d271212 p = 1) : d369931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45905 q = 1) (hb : d271211 q = 1) : d46042 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d46042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104639 q ha hb
    | true =>
      simp only [d45905, d46042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68906 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45906 q = 1) (hb : d271212 q = 1) : d46043 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d271212, d46043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45906, d271212, d46043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45907 q = 1) (hb : d271212 q = 1) : d46053 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45907, d46053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45907, d46053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d45571 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104692 q ha hb
    | true =>
      simp only [d45571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45572 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45572, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d45574 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104693 q ha hb
    | true =>
      simp only [d45574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d45575 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45575, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d45576 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45908 q = 1) (hb : d271212 q = 1) : d46054 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45908, d46054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45908, d46054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45909 q = 1) (hb : d271212 q = 1) : d46055 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45909, d46055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45909, d46055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46043 q = 1) (hb : d271212 q = 1) : d46043 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d45591 q = 1) (hb : d271211 q = 1) : d369385 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45591, d369385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104695 q ha hb
    | true =>
      simp only [d45591, d369385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d45592 q = 1) (hb : d271212 q = 1) : d369386 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45592, d271212, d369386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45592, d271212, d369386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d46044 q = 1) (hb : d271212 q = 1) : d369497 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46044, d369497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46044, d369497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46045 q = 1) (hb : d271212 q = 1) : d369689 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46045, d369689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46045, d369689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46046 q = 1) (hb : d271212 q = 1) : d369690 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46046, d369690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d46046, d369690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d46047 q = 1) (hb : d271212 q = 1) : d369931 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46047, d369931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46047, d369931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104754 (p : Pattern) (ha : d46056 p = 1) (hb : d271212 p = 1) : d369931 p = 1 := by
  have h0 (q : Pattern) (ha : d46055 q = 1) (hb : d271212 q = 1) : d46055 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46043 q = 1) (hb : d271212 q = 1) : d46043 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45591 q = 1) (hb : d271211 q = 1) : d369385 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45591, d369385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104695 q ha hb
    | true =>
      simp only [d45591, d369385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45592 q = 1) (hb : d271212 q = 1) : d369386 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45592, d271212, d369386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45592, d271212, d369386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46044 q = 1) (hb : d271212 q = 1) : d369497 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46044, d369497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46044, d369497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d46045 q = 1) (hb : d271212 q = 1) : d369689 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46045, d369689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46045, d369689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46046 q = 1) (hb : d271212 q = 1) : d369690 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46046, d369690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46046, d369690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d46056 q = 1) (hb : d271212 q = 1) : d369931 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46056, d369931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46056, d369931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104755 (p : Pattern) (ha : d46062 p = 1) (hb : d271212 p = 1) : d369938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46036 q = 1) (hb : d271212 q = 1) : d369927 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46036, d369927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104752 q ha hb
    | true =>
      simp only [d46036, d369927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46037 q = 1) (hb : d271212 q = 1) : d369928 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46037, d369928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46037, d369928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46038 q = 1) (hb : d271212 q = 1) : d369929 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46038, d369929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46038, d369929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46039 q = 1) (hb : d271212 q = 1) : d369930 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46039, d369930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46039, d369930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46048 q = 1) (hb : d271212 q = 1) : d369932 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46048, d369932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104753 q ha hb
    | true =>
      simp only [d46048, d369932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46049 q = 1) (hb : d271212 q = 1) : d369933 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46049, d369933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46049, d369933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46050 q = 1) (hb : d271212 q = 1) : d369934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46050, d369934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46050, d369934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46051 q = 1) (hb : d271212 q = 1) : d369935 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46051, d369935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46051, d369935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46052 q = 1) (hb : d271212 q = 1) : d369936 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46052, d369936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46052, d369936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46057 q = 1) (hb : d271212 q = 1) : d369932 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46057, d369932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104754 q ha hb
    | true =>
      simp only [d46057, d369932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46058 q = 1) (hb : d271212 q = 1) : d369933 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46058, d369933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46058, d369933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46059 q = 1) (hb : d271212 q = 1) : d369934 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46059, d369934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46059, d369934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46060 q = 1) (hb : d271212 q = 1) : d369935 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46060, d369935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46060, d369935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45937 q = 1) (hb : d271212 q = 1) : d369692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45937, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104725 q ha hb
    | true =>
      simp only [d45937, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45938 q = 1) (hb : d271212 q = 1) : d369693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45938, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45938, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45939 q = 1) (hb : d271212 q = 1) : d369694 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45939, d369694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45939, d369694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45940 q = 1) (hb : d271212 q = 1) : d369695 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45940, d369695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45940, d369695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46061 q = 1) (hb : d271212 q = 1) : d369937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46061, d369937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46061, d369937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46062 q = 1) (hb : d271212 q = 1) : d369938 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46062, d369938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46062, d369938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104756 (p : Pattern) (ha : d46069 p = 1) (hb : d271212 p = 1) : d369691 p = 1 := by
  have h0 (q : Pattern) (ha : d45905 q = 1) (hb : d271211 q = 1) : d46042 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d46042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104639 q ha hb
    | true =>
      simp only [d45905, d46042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68906 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45906 q = 1) (hb : d271212 q = 1) : d46043 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d271212, d46043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45906, d271212, d46043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45922 q = 1) (hb : d271211 q = 1) : d369385 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45922, d369385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104695 q ha hb
    | true =>
      simp only [d45922, d369385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68908 q ha hb
  have h4 (q : Pattern) (ha : d45923 q = 1) (hb : d271212 q = 1) : d369386 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45923, d271212, d369386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45923, d271212, d369386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d46066 q = 1) (hb : d271212 q = 1) : d369497 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46066, d369497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46066, d369497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46067 q = 1) (hb : d271212 q = 1) : d369689 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46067, d369689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46067, d369689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46068 q = 1) (hb : d271212 q = 1) : d369690 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46068, d369690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46068, d369690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d44885 q = 1) (hb : d271211 q = 1) : d46477 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104581 q ha hb
    | true =>
      simp only [d44885, d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44886 q = 1) (hb : d271212 q = 1) : d179204 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d271212, d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44886, d271212, d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d45924 q = 1) (hb : d271212 q = 1) : d369387 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45924, d369387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45924, d369387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45925 q = 1) (hb : d271212 q = 1) : d369509 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45925, d369509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45925, d369509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d45926 q = 1) (hb : d271212 q = 1) : d369510 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45926, d369510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45926, d369510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d46069 q = 1) (hb : d271212 q = 1) : d369691 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46069, d369691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46069, d369691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104757 (p : Pattern) (ha : d46075 p = 1) (hb : d271212 p = 1) : d369942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46070 q = 1) (hb : d271212 q = 1) : d369692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46070, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104756 q ha hb
    | true =>
      simp only [d46070, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46071 q = 1) (hb : d271212 q = 1) : d369693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46071, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46071, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46072 q = 1) (hb : d271212 q = 1) : d369694 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46072, d369694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46072, d369694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46073 q = 1) (hb : d271212 q = 1) : d369695 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46073, d369695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46073, d369695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45946 q = 1) (hb : d271212 q = 1) : d369856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104726 q ha hb
    | true =>
      simp only [d45946, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45947 q = 1) (hb : d271212 q = 1) : d369857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45947, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45948 q = 1) (hb : d271212 q = 1) : d369858 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45948, d369858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45948, d369858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45949 q = 1) (hb : d271212 q = 1) : d369859 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45949, d369859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45949, d369859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46074 q = 1) (hb : d271212 q = 1) : d369860 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46074, d369860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46074, d369860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45968 q = 1) (hb : d271212 q = 1) : d369863 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45968, d369863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45968, d369863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46075 q = 1) (hb : d271212 q = 1) : d369942 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46075, d369942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46075, d369942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104758 (p : Pattern) (ha : d46081 p = 1) (hb : d271212 p = 1) : d369948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46063 q = 1) (hb : d271212 q = 1) : d369939 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46063, d369939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104755 q ha hb
    | true =>
      simp only [d46063, d369939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104727 q ha hb
  have h2 (q : Pattern) (ha : d46064 q = 1) (hb : d271212 q = 1) : d369940 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46064, d369940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46064, d369940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46065 q = 1) (hb : d271212 q = 1) : d369941 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46065, d369941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46065, d369941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46076 q = 1) (hb : d271212 q = 1) : d369943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46076, d369943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104727 q ha hb
    | true =>
      simp only [d46076, d369943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104757 q ha hb
  have h5 (q : Pattern) (ha : d46077 q = 1) (hb : d271212 q = 1) : d369944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46077, d369944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46077, d369944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46078 q = 1) (hb : d271212 q = 1) : d369945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46078, d369945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46078, d369945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46079 q = 1) (hb : d271212 q = 1) : d369946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46079, d369946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46079, d369946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45970 q = 1) (hb : d271212 q = 1) : d369865 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45970, d369865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104727 q ha hb
    | true =>
      simp only [d45970, d369865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104730 q ha hb
  have h9 (q : Pattern) (ha : d45971 q = 1) (hb : d271212 q = 1) : d369866 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45971, d369866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45971, d369866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45972 q = 1) (hb : d271212 q = 1) : d369867 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45972, d369867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45972, d369867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45975 q = 1) (hb : d271212 q = 1) : d369869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45975, d369869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104730 q ha hb
    | true =>
      simp only [d45975, d369869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104731 q ha hb
  have h12 (q : Pattern) (ha : d45976 q = 1) (hb : d271212 q = 1) : d369870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45976, d369870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45976, d369870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45977 q = 1) (hb : d271212 q = 1) : d369871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45977, d369871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45977, d369871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45978 q = 1) (hb : d271212 q = 1) : d369872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45978, d369872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45978, d369872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46080 q = 1) (hb : d271212 q = 1) : d369947 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46080, d369947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46080, d369947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46081 q = 1) (hb : d271212 q = 1) : d369948 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46081, d369948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46081, d369948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro104759 (p : Pattern) (ha : d46087 p = 1) (hb : d271212 p = 1) : d369954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46082 q = 1) (hb : d271212 q = 1) : d369949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46082, d369949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104758 q ha hb
    | true =>
      simp only [d46082, d369949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46083 q = 1) (hb : d271212 q = 1) : d369950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46083, d369950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46083, d369950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45982 q = 1) (hb : d271212 q = 1) : d369876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104732 q ha hb
    | true =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45983 q = 1) (hb : d271212 q = 1) : d369877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46084 q = 1) (hb : d271212 q = 1) : d369951 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46084, d369951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46084, d369951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46085 q = 1) (hb : d271212 q = 1) : d369952 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46085, d369952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46085, d369952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46086 q = 1) (hb : d271212 q = 1) : d369953 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46086, d369953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46086, d369953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46087 q = 1) (hb : d271212 q = 1) : d369954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46087, d369954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46087, d369954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104760 (p : Pattern) (ha : d46197 p = 1) (hb : d271212 p = 1) : d369868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45963 q = 1) (hb : d271212 q = 1) : d369856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104729 q ha hb
    | true =>
      simp only [d45963, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45964 q = 1) (hb : d271212 q = 1) : d369857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45964, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45965 q = 1) (hb : d271212 q = 1) : d369858 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45965, d369858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45965, d369858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45966 q = 1) (hb : d271212 q = 1) : d369859 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45966, d369859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45966, d369859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45973 q = 1) (hb : d271212 q = 1) : d369863 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45973, d369863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45973, d369863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46197 q = 1) (hb : d271212 q = 1) : d369868 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46197, d369868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46197, d369868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104761 (p : Pattern) (ha : d46203 p = 1) (hb : d271212 p = 1) : d369875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45970 q = 1) (hb : d271212 q = 1) : d369865 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45970, d369865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104727 q ha hb
    | true =>
      simp only [d45970, d369865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104730 q ha hb
  have h2 (q : Pattern) (ha : d45971 q = 1) (hb : d271212 q = 1) : d369866 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45971, d369866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45971, d369866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45972 q = 1) (hb : d271212 q = 1) : d369867 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45972, d369867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45972, d369867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45975 q = 1) (hb : d271212 q = 1) : d369869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45975, d369869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104730 q ha hb
    | true =>
      simp only [d45975, d369869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104731 q ha hb
  have h5 (q : Pattern) (ha : d45976 q = 1) (hb : d271212 q = 1) : d369870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45976, d369870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45976, d369870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45977 q = 1) (hb : d271212 q = 1) : d369871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45977, d369871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45977, d369871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45978 q = 1) (hb : d271212 q = 1) : d369872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45978, d369872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45978, d369872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46198 q = 1) (hb : d271212 q = 1) : d369869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46198, d369869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104730 q ha hb
    | true =>
      simp only [d46198, d369869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104760 q ha hb
  have h9 (q : Pattern) (ha : d46199 q = 1) (hb : d271212 q = 1) : d369870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46199, d369870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46199, d369870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46200 q = 1) (hb : d271212 q = 1) : d369871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46200, d369871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46200, d369871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46201 q = 1) (hb : d271212 q = 1) : d369873 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46201, d369873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46201, d369873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46202 q = 1) (hb : d271212 q = 1) : d369874 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46202, d369874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46202, d369874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46203 q = 1) (hb : d271212 q = 1) : d369875 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46203, d369875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46203, d369875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro104762 (p : Pattern) (ha : d46209 p = 1) (hb : d271212 p = 1) : d369960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46204 q = 1) (hb : d271212 q = 1) : d369876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46204, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104761 q ha hb
    | true =>
      simp only [d46204, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46205 q = 1) (hb : d271212 q = 1) : d369877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46205, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46205, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46206 q = 1) (hb : d271212 q = 1) : d369957 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46206, d369957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46206, d369957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46207 q = 1) (hb : d271212 q = 1) : d369958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46207, d369958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46207, d369958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46208 q = 1) (hb : d271212 q = 1) : d369959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46208, d369959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46208, d369959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46209 q = 1) (hb : d271212 q = 1) : d369960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46209, d369960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46209, d369960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104763 (p : Pattern) (ha : d271212 p = 1) (hb : d322168 p = 1) : d369966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46019 q = 1) (hb : d271212 q = 1) : d369913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46019, d369913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104748 q ha hb
    | true =>
      simp only [d46019, d369913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104749 q ha hb
  have h2 (q : Pattern) (ha : d46020 q = 1) (hb : d271212 q = 1) : d369914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46020, d369914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46020, d369914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46021 q = 1) (hb : d271212 q = 1) : d369915 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46021, d369915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46021, d369915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46022 q = 1) (hb : d271212 q = 1) : d369916 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46022, d369916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46022, d369916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46029 q = 1) (hb : d271212 q = 1) : d369923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46029, d369923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104750 q ha hb
    | true =>
      simp only [d46029, d369923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104751 q ha hb
  have h6 (q : Pattern) (ha : d46030 q = 1) (hb : d271212 q = 1) : d369924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46030, d369924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46030, d369924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46031 q = 1) (hb : d271212 q = 1) : d369925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46031, d369925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46031, d369925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46088 q = 1) (hb : d271212 q = 1) : d369955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46088, d369955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104759 q ha hb
    | true =>
      simp only [d46088, d369955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104734 q ha hb
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d322164 q = 1) : d369956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322164, d369956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d322164, d369956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46210 q = 1) (hb : d271212 q = 1) : d369961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46210, d369961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104762 q ha hb
    | true =>
      simp only [d46210, d369961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46211 q = 1) (hb : d271212 q = 1) : d369962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46211, d369962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46211, d369962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d322165 q = 1) : d369963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322165, d369963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322165, d369963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d322166 q = 1) : d369964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322166, d369964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d322166, d369964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d322167 q = 1) : d369965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322167, d369965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322167, d369965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d322168 q = 1) : d369966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322168, d369966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322168, d369966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104764 (p : Pattern) (ha : d46216 p = 1) (hb : d271212 p = 1) : d369967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d271212 q = 1) : d369876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104732 q ha hb
    | true =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d271212 q = 1) : d369877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d271212 q = 1) : d369880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104733 q ha hb
    | true =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d271212 q = 1) : d369881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d271212 q = 1) : d369882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d369882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d369882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45989 q = 1) (hb : d271212 q = 1) : d369883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45989, d369883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45989, d369883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46015 q = 1) (hb : d271212 q = 1) : d369909 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46015, d369909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46015, d369909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46216 q = 1) (hb : d271212 q = 1) : d369967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46216, d369967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46216, d369967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104765 (p : Pattern) (ha : d46217 p = 1) (hb : d271212 p = 1) : d369968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d271212 q = 1) : d369880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104733 q ha hb
    | true =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d271212 q = 1) : d369881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d271212 q = 1) : d369886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d369886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d369886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45993 q = 1) (hb : d271212 q = 1) : d369887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45993, d369887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45993, d369887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46017 q = 1) (hb : d271212 q = 1) : d369911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46017, d369911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46017, d369911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46217 q = 1) (hb : d271212 q = 1) : d369968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46217, d369968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46217, d369968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104766 (p : Pattern) (ha : d46222 p = 1) (hb : d271212 p = 1) : d369973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d271212 q = 1) : d369876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104732 q ha hb
    | true =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d271212 q = 1) : d369877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d271212 q = 1) : d369880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104733 q ha hb
    | true =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d271212 q = 1) : d369881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d271212 q = 1) : d369882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d369882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d369882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46023 q = 1) (hb : d271212 q = 1) : d369917 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46023, d369917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46023, d369917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46024 q = 1) (hb : d271212 q = 1) : d369918 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46024, d369918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46024, d369918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46222 q = 1) (hb : d271212 q = 1) : d369973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46222, d369973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46222, d369973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104767 (p : Pattern) (ha : d46223 p = 1) (hb : d271212 p = 1) : d369974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d271212 q = 1) : d369880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104733 q ha hb
    | true =>
      simp only [d45986, d369880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d271212 q = 1) : d369881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d369881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d271212 q = 1) : d369886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d369886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d369886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46026 q = 1) (hb : d271212 q = 1) : d369920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46026, d369920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46026, d369920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46027 q = 1) (hb : d271212 q = 1) : d369921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46027, d369921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46027, d369921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46223 q = 1) (hb : d271212 q = 1) : d369974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46223, d369974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46223, d369974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104768 (p : Pattern) (ha : d46227 p = 1) (hb : d271212 p = 1) : d369978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46082 q = 1) (hb : d271212 q = 1) : d369949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46082, d369949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104758 q ha hb
    | true =>
      simp only [d46082, d369949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46083 q = 1) (hb : d271212 q = 1) : d369950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46083, d369950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46083, d369950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45982 q = 1) (hb : d271212 q = 1) : d369876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104732 q ha hb
    | true =>
      simp only [d45982, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45983 q = 1) (hb : d271212 q = 1) : d369877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46084 q = 1) (hb : d271212 q = 1) : d369951 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46084, d369951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46084, d369951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46085 q = 1) (hb : d271212 q = 1) : d369952 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46085, d369952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46085, d369952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46086 q = 1) (hb : d271212 q = 1) : d369953 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46086, d369953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46086, d369953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46227 q = 1) (hb : d271212 q = 1) : d369978 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46227, d369978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46227, d369978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104769 (p : Pattern) (ha : d46233 p = 1) (hb : d271212 p = 1) : d369981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46204 q = 1) (hb : d271212 q = 1) : d369876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46204, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104761 q ha hb
    | true =>
      simp only [d46204, d369876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46205 q = 1) (hb : d271212 q = 1) : d369877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46205, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46205, d369877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46206 q = 1) (hb : d271212 q = 1) : d369957 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46206, d369957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46206, d369957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46207 q = 1) (hb : d271212 q = 1) : d369958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46207, d369958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46207, d369958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46208 q = 1) (hb : d271212 q = 1) : d369959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46208, d369959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46208, d369959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46233 q = 1) (hb : d271212 q = 1) : d369981 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46233, d369981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46233, d369981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104770 (p : Pattern) (ha : d271212 p = 1) (hb : d322173 p = 1) : d369987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46019 q = 1) (hb : d271212 q = 1) : d369913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46019, d369913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104748 q ha hb
    | true =>
      simp only [d46019, d369913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104749 q ha hb
  have h2 (q : Pattern) (ha : d46020 q = 1) (hb : d271212 q = 1) : d369914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46020, d369914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46020, d369914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46021 q = 1) (hb : d271212 q = 1) : d369915 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46021, d369915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46021, d369915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46022 q = 1) (hb : d271212 q = 1) : d369916 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46022, d369916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46022, d369916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46029 q = 1) (hb : d271212 q = 1) : d369923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46029, d369923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104750 q ha hb
    | true =>
      simp only [d46029, d369923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104751 q ha hb
  have h6 (q : Pattern) (ha : d46030 q = 1) (hb : d271212 q = 1) : d369924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46030, d369924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46030, d369924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46031 q = 1) (hb : d271212 q = 1) : d369925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46031, d369925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46031, d369925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46088 q = 1) (hb : d271212 q = 1) : d369955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46088, d369955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104759 q ha hb
    | true =>
      simp only [d46088, d369955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104734 q ha hb
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d322164 q = 1) : d369956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322164, d369956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d322164, d369956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46210 q = 1) (hb : d271212 q = 1) : d369961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46210, d369961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104762 q ha hb
    | true =>
      simp only [d46210, d369961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46211 q = 1) (hb : d271212 q = 1) : d369962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46211, d369962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46211, d369962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d322165 q = 1) : d369963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322165, d369963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322165, d369963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d322166 q = 1) : d369964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322166, d369964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d322166, d369964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d322167 q = 1) : d369965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322167, d369965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322167, d369965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46218 q = 1) (hb : d271212 q = 1) : d369969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46218, d369969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104764 q ha hb
    | true =>
      simp only [d46218, d369969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104765 q ha hb
  have h16 (q : Pattern) (ha : d46219 q = 1) (hb : d271212 q = 1) : d369970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46219, d369970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46219, d369970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46220 q = 1) (hb : d271212 q = 1) : d369971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46220, d369971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46220, d369971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46221 q = 1) (hb : d271212 q = 1) : d369972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46221, d369972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46221, d369972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46224 q = 1) (hb : d271212 q = 1) : d369975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46224, d369975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104766 q ha hb
    | true =>
      simp only [d46224, d369975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104767 q ha hb
  have h20 (q : Pattern) (ha : d46225 q = 1) (hb : d271212 q = 1) : d369976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46225, d369976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46225, d369976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d46226 q = 1) (hb : d271212 q = 1) : d369977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46226, d369977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d46226, d369977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d46228 q = 1) (hb : d271212 q = 1) : d369979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46228, d369979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104768 q ha hb
    | true =>
      simp only [d46228, d369979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104737 q ha hb
  have h23 (q : Pattern) (ha : d271212 q = 1) (hb : d322169 q = 1) : d369980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322169, d369980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d322169, d369980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d46234 q = 1) (hb : d271212 q = 1) : d369982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46234, d369982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104769 q ha hb
    | true =>
      simp only [d46234, d369982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d46235 q = 1) (hb : d271212 q = 1) : d369983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46235, d369983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d46235, d369983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d271212 q = 1) (hb : d322170 q = 1) : d369984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322170, d369984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d322170, d369984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d271212 q = 1) (hb : d322171 q = 1) : d369985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322171, d369985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d322171, d369985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d271212 q = 1) (hb : d322172 q = 1) : d369986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322172, d369986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d322172, d369986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d271212 q = 1) (hb : d322173 q = 1) : d369987 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322173, d369987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322173, d369987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro104771 (p : Pattern) (ha : d271212 p = 1) (hb : d322180 p = 1) : d370007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46228 q = 1) (hb : d271212 q = 1) : d369979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46228, d369979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104768 q ha hb
    | true =>
      simp only [d46228, d369979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104737 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322169 q = 1) : d369980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322169, d369980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322169, d369980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46234 q = 1) (hb : d271212 q = 1) : d369982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46234, d369982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104769 q ha hb
    | true =>
      simp only [d46234, d369982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46235 q = 1) (hb : d271212 q = 1) : d369983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46235, d369983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46235, d369983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322170 q = 1) : d369984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322170, d369984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322170, d369984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322178 q = 1) : d370005 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322178, d370005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322178, d370005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d322179 q = 1) : d370006 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322179, d370006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322179, d370006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d322180 q = 1) : d370007 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322180, d370007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322180, d370007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104772 (p : Pattern) (ha : d46285 p = 1) (hb : d271212 p = 1) : d370025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46267 q = 1) (hb : d271212 q = 1) : d370015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46267, d370015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46267, d370015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104752 q ha hb
  have h2 (q : Pattern) (ha : d46036 q = 1) (hb : d271212 q = 1) : d369927 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46036, d369927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104752 q ha hb
    | true =>
      simp only [d46036, d369927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46268 q = 1) (hb : d271212 q = 1) : d370016 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46268, d370016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46268, d370016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46037 q = 1) (hb : d271212 q = 1) : d369928 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46037, d369928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46037, d369928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46269 q = 1) (hb : d271212 q = 1) : d370017 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46269, d370017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46269, d370017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46270 q = 1) (hb : d271212 q = 1) : d370018 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46270, d370018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46270, d370018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46271 q = 1) (hb : d271212 q = 1) : d370019 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46271, d370019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46271, d370019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104753 q ha hb
  have h8 (q : Pattern) (ha : d46048 q = 1) (hb : d271212 q = 1) : d369932 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46048, d369932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104753 q ha hb
    | true =>
      simp only [d46048, d369932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46272 q = 1) (hb : d271212 q = 1) : d370020 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46272, d370020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46272, d370020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46049 q = 1) (hb : d271212 q = 1) : d369933 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46049, d369933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46049, d369933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46273 q = 1) (hb : d271212 q = 1) : d370021 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46273, d370021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46273, d370021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46274 q = 1) (hb : d271212 q = 1) : d370022 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46274, d370022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46274, d370022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46275 q = 1) (hb : d271212 q = 1) : d370023 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46275, d370023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46275, d370023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46276 q = 1) (hb : d271212 q = 1) : d370019 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46276, d370019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46276, d370019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104754 q ha hb
  have h15 (q : Pattern) (ha : d46057 q = 1) (hb : d271212 q = 1) : d369932 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46057, d369932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104754 q ha hb
    | true =>
      simp only [d46057, d369932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d46277 q = 1) (hb : d271212 q = 1) : d370020 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46277, d370020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d46277, d370020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46058 q = 1) (hb : d271212 q = 1) : d369933 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46058, d369933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46058, d369933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46278 q = 1) (hb : d271212 q = 1) : d370021 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46278, d370021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46278, d370021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46279 q = 1) (hb : d271212 q = 1) : d370022 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46279, d370022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d46279, d370022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d46280 q = 1) (hb : d271212 q = 1) : d369783 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46280, d369783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46280, d369783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104725 q ha hb
  have h21 (q : Pattern) (ha : d45937 q = 1) (hb : d271212 q = 1) : d369692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45937, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104725 q ha hb
    | true =>
      simp only [d45937, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d46281 q = 1) (hb : d271212 q = 1) : d369784 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46281, d369784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d46281, d369784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d45938 q = 1) (hb : d271212 q = 1) : d369693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45938, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45938, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d46282 q = 1) (hb : d271212 q = 1) : d369785 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46282, d369785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d46282, d369785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d46283 q = 1) (hb : d271212 q = 1) : d369786 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46283, d369786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d46283, d369786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46284 q = 1) (hb : d271212 q = 1) : d370024 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46284, d370024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d46284, d370024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d46285 q = 1) (hb : d271212 q = 1) : d370025 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46285, d370025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46285, d370025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro104773 (p : Pattern) (ha : d46300 p = 1) (hb : d271212 p = 1) : d370031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46286 q = 1) (hb : d271212 q = 1) : d369774 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46286, d369774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46286, d369774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104723 q ha hb
  have h2 (q : Pattern) (ha : d45916 q = 1) (hb : d271212 q = 1) : d369679 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45916, d369679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104723 q ha hb
    | true =>
      simp only [d45916, d369679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46287 q = 1) (hb : d271212 q = 1) : d369775 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46287, d369775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46287, d369775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45917 q = 1) (hb : d271212 q = 1) : d369680 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45917, d369680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45917, d369680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46288 q = 1) (hb : d271212 q = 1) : d369776 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46288, d369776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46288, d369776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46289 q = 1) (hb : d271212 q = 1) : d369777 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46289, d369777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46289, d369777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46290 q = 1) (hb : d271212 q = 1) : d369778 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46290, d369778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46290, d369778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104724 q ha hb
  have h8 (q : Pattern) (ha : d45928 q = 1) (hb : d271212 q = 1) : d369684 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45928, d369684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104724 q ha hb
    | true =>
      simp only [d45928, d369684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46291 q = 1) (hb : d271212 q = 1) : d369779 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46291, d369779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46291, d369779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45929 q = 1) (hb : d271212 q = 1) : d369685 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45929, d369685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45929, d369685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46292 q = 1) (hb : d271212 q = 1) : d369780 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46292, d369780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46292, d369780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46293 q = 1) (hb : d271212 q = 1) : d369781 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46293, d369781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46293, d369781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46294 q = 1) (hb : d271212 q = 1) : d369782 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46294, d369782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46294, d369782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46280 q = 1) (hb : d271212 q = 1) : d369783 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46280, d369783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46280, d369783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104725 q ha hb
  have h15 (q : Pattern) (ha : d45937 q = 1) (hb : d271212 q = 1) : d369692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45937, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104725 q ha hb
    | true =>
      simp only [d45937, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d46281 q = 1) (hb : d271212 q = 1) : d369784 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46281, d369784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d46281, d369784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45938 q = 1) (hb : d271212 q = 1) : d369693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45938, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45938, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46282 q = 1) (hb : d271212 q = 1) : d369785 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46282, d369785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46282, d369785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46283 q = 1) (hb : d271212 q = 1) : d369786 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46283, d369786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d46283, d369786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d46295 q = 1) (hb : d271212 q = 1) : d370026 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46295, d370026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46295, d370026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104726 q ha hb
  have h21 (q : Pattern) (ha : d45946 q = 1) (hb : d271212 q = 1) : d369856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104726 q ha hb
    | true =>
      simp only [d45946, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d46296 q = 1) (hb : d271212 q = 1) : d370027 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46296, d370027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d46296, d370027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d45947 q = 1) (hb : d271212 q = 1) : d369857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45947, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d46297 q = 1) (hb : d271212 q = 1) : d370028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46297, d370028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d46297, d370028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d46298 q = 1) (hb : d271212 q = 1) : d370029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46298, d370029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d46298, d370029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46299 q = 1) (hb : d271212 q = 1) : d370030 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46299, d370030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d46299, d370030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d46300 q = 1) (hb : d271212 q = 1) : d370031 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46300, d370031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46300, d370031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro104774 (p : Pattern) (ha : d46310 p = 1) (hb : d271212 p = 1) : d370036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46304 q = 1) (hb : d271212 q = 1) : d369783 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46304, d369783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46304, d369783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104756 q ha hb
  have h2 (q : Pattern) (ha : d46070 q = 1) (hb : d271212 q = 1) : d369692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46070, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104756 q ha hb
    | true =>
      simp only [d46070, d369692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46305 q = 1) (hb : d271212 q = 1) : d369784 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46305, d369784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46305, d369784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46071 q = 1) (hb : d271212 q = 1) : d369693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46071, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46071, d369693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46306 q = 1) (hb : d271212 q = 1) : d369785 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46306, d369785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46306, d369785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46307 q = 1) (hb : d271212 q = 1) : d369786 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46307, d369786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46307, d369786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46295 q = 1) (hb : d271212 q = 1) : d370026 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46295, d370026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46295, d370026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104726 q ha hb
  have h8 (q : Pattern) (ha : d45946 q = 1) (hb : d271212 q = 1) : d369856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104726 q ha hb
    | true =>
      simp only [d45946, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46296 q = 1) (hb : d271212 q = 1) : d370027 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46296, d370027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46296, d370027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45947 q = 1) (hb : d271212 q = 1) : d369857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45947, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46297 q = 1) (hb : d271212 q = 1) : d370028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46297, d370028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46297, d370028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46298 q = 1) (hb : d271212 q = 1) : d370029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46298, d370029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46298, d370029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46308 q = 1) (hb : d271212 q = 1) : d370030 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46308, d370030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46308, d370030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46309 q = 1) (hb : d271212 q = 1) : d370035 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46309, d370035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46309, d370035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46310 q = 1) (hb : d271212 q = 1) : d370036 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46310, d370036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46310, d370036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104775 (p : Pattern) (ha : d46335 p = 1) (hb : d271212 p = 1) : d370052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46301 q = 1) (hb : d271212 q = 1) : d370032 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46301, d370032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104772 q ha hb
    | true =>
      simp only [d46301, d370032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104773 q ha hb
  have h2 (q : Pattern) (ha : d46302 q = 1) (hb : d271212 q = 1) : d370033 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46302, d370033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46302, d370033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46303 q = 1) (hb : d271212 q = 1) : d370034 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46303, d370034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46303, d370034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46311 q = 1) (hb : d271212 q = 1) : d370037 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46311, d370037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104773 q ha hb
    | true =>
      simp only [d46311, d370037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104774 q ha hb
  have h5 (q : Pattern) (ha : d46312 q = 1) (hb : d271212 q = 1) : d370038 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46312, d370038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46312, d370038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46313 q = 1) (hb : d271212 q = 1) : d370039 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46313, d370039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46313, d370039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46314 q = 1) (hb : d271212 q = 1) : d370040 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46314, d370040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46314, d370040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46325 q = 1) (hb : d271212 q = 1) : d370043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d370043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104773 q ha hb
    | true =>
      simp only [d46325, d370043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104743 q ha hb
  have h9 (q : Pattern) (ha : d46326 q = 1) (hb : d271212 q = 1) : d370044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d370044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46326, d370044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46327 q = 1) (hb : d271212 q = 1) : d370045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d370045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46327, d370045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46330 q = 1) (hb : d271212 q = 1) : d370047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d370047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104743 q ha hb
    | true =>
      simp only [d46330, d370047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104744 q ha hb
  have h12 (q : Pattern) (ha : d46331 q = 1) (hb : d271212 q = 1) : d370048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d370048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46331, d370048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46332 q = 1) (hb : d271212 q = 1) : d370049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d370049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46332, d370049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46333 q = 1) (hb : d271212 q = 1) : d370050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d370050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46333, d370050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46334 q = 1) (hb : d271212 q = 1) : d370051 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46334, d370051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46334, d370051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46335 q = 1) (hb : d271212 q = 1) : d370052 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46335, d370052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46335, d370052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro104776 (p : Pattern) (ha : d46340 p = 1) (hb : d271212 p = 1) : d370057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46325 q = 1) (hb : d271212 q = 1) : d370043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d370043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104773 q ha hb
    | true =>
      simp only [d46325, d370043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104743 q ha hb
  have h2 (q : Pattern) (ha : d46326 q = 1) (hb : d271212 q = 1) : d370044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d370044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46326, d370044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46327 q = 1) (hb : d271212 q = 1) : d370045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d370045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46327, d370045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46330 q = 1) (hb : d271212 q = 1) : d370047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d370047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104743 q ha hb
    | true =>
      simp only [d46330, d370047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104744 q ha hb
  have h5 (q : Pattern) (ha : d46331 q = 1) (hb : d271212 q = 1) : d370048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d370048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46331, d370048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46332 q = 1) (hb : d271212 q = 1) : d370049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d370049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46332, d370049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46333 q = 1) (hb : d271212 q = 1) : d370050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d370050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46333, d370050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46338 q = 1) (hb : d271212 q = 1) : d370055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46338, d370055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46338, d370055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46339 q = 1) (hb : d271212 q = 1) : d370056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46339, d370056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46339, d370056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46340 q = 1) (hb : d271212 q = 1) : d370057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46340, d370057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46340, d370057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro104777 (p : Pattern) (ha : d46346 p = 1) (hb : d271212 p = 1) : d370063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46336 q = 1) (hb : d271212 q = 1) : d370053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46336, d370053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104775 q ha hb
    | true =>
      simp only [d46336, d370053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46337 q = 1) (hb : d271212 q = 1) : d370054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46337, d370054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46337, d370054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46341 q = 1) (hb : d271212 q = 1) : d370058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46341, d370058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104776 q ha hb
    | true =>
      simp only [d46341, d370058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46342 q = 1) (hb : d271212 q = 1) : d370059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46342, d370059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46342, d370059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46343 q = 1) (hb : d271212 q = 1) : d370060 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46343, d370060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46343, d370060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46344 q = 1) (hb : d271212 q = 1) : d370061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46344, d370061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46344, d370061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46345 q = 1) (hb : d271212 q = 1) : d370062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46345, d370062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46345, d370062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46346 q = 1) (hb : d271212 q = 1) : d370063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46346, d370063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46346, d370063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104778 (p : Pattern) (ha : d46354 p = 1) (hb : d271212 p = 1) : d370071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46341 q = 1) (hb : d271212 q = 1) : d370058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46341, d370058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104776 q ha hb
    | true =>
      simp only [d46341, d370058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46342 q = 1) (hb : d271212 q = 1) : d370059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46342, d370059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46342, d370059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46349 q = 1) (hb : d271212 q = 1) : d370066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46349, d370066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104745 q ha hb
    | true =>
      simp only [d46349, d370066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46350 q = 1) (hb : d271212 q = 1) : d370067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46350, d370067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46350, d370067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46351 q = 1) (hb : d271212 q = 1) : d370068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46351, d370068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46351, d370068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46352 q = 1) (hb : d271212 q = 1) : d370069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46352, d370069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46352, d370069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46353 q = 1) (hb : d271212 q = 1) : d370070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46353, d370070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46353, d370070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46354 q = 1) (hb : d271212 q = 1) : d370071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46354, d370071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46354, d370071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104779 (p : Pattern) (ha : d46414 p = 1) (hb : d271212 p = 1) : d370046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46319 q = 1) (hb : d271212 q = 1) : d370026 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46319, d370026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46319, d370026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104729 q ha hb
  have h2 (q : Pattern) (ha : d45963 q = 1) (hb : d271212 q = 1) : d369856 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104729 q ha hb
    | true =>
      simp only [d45963, d369856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46320 q = 1) (hb : d271212 q = 1) : d370027 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46320, d370027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46320, d370027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45964 q = 1) (hb : d271212 q = 1) : d369857 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45964, d369857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46321 q = 1) (hb : d271212 q = 1) : d370028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46321, d370028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46321, d370028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46322 q = 1) (hb : d271212 q = 1) : d370029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46322, d370029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46322, d370029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46328 q = 1) (hb : d271212 q = 1) : d370035 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46328, d370035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46328, d370035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46414 q = 1) (hb : d271212 q = 1) : d370046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46414, d370046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46414, d370046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104780 (p : Pattern) (ha : d46420 p = 1) (hb : d271212 p = 1) : d370057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46325 q = 1) (hb : d271212 q = 1) : d370043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d370043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104773 q ha hb
    | true =>
      simp only [d46325, d370043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104743 q ha hb
  have h2 (q : Pattern) (ha : d46326 q = 1) (hb : d271212 q = 1) : d370044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d370044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46326, d370044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46327 q = 1) (hb : d271212 q = 1) : d370045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d370045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46327, d370045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46330 q = 1) (hb : d271212 q = 1) : d370047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d370047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104743 q ha hb
    | true =>
      simp only [d46330, d370047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104744 q ha hb
  have h5 (q : Pattern) (ha : d46331 q = 1) (hb : d271212 q = 1) : d370048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d370048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46331, d370048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46332 q = 1) (hb : d271212 q = 1) : d370049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d370049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46332, d370049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46333 q = 1) (hb : d271212 q = 1) : d370050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d370050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46333, d370050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46415 q = 1) (hb : d271212 q = 1) : d370047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46415, d370047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104743 q ha hb
    | true =>
      simp only [d46415, d370047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104779 q ha hb
  have h9 (q : Pattern) (ha : d46416 q = 1) (hb : d271212 q = 1) : d370048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46416, d370048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46416, d370048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46417 q = 1) (hb : d271212 q = 1) : d370049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46417, d370049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46417, d370049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46418 q = 1) (hb : d271212 q = 1) : d370055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46418, d370055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46418, d370055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46419 q = 1) (hb : d271212 q = 1) : d370056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46419, d370056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46419, d370056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46420 q = 1) (hb : d271212 q = 1) : d370057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46420, d370057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46420, d370057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro104781 (p : Pattern) (ha : d46426 p = 1) (hb : d271212 p = 1) : d370077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46421 q = 1) (hb : d271212 q = 1) : d370058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46421, d370058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104780 q ha hb
    | true =>
      simp only [d46421, d370058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46422 q = 1) (hb : d271212 q = 1) : d370059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46422, d370059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46422, d370059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46423 q = 1) (hb : d271212 q = 1) : d370074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46423, d370074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46423, d370074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46424 q = 1) (hb : d271212 q = 1) : d370075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46424, d370075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46424, d370075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46425 q = 1) (hb : d271212 q = 1) : d370076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46425, d370076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46425, d370076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46426 q = 1) (hb : d271212 q = 1) : d370077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46426, d370077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46426, d370077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104782 (p : Pattern) (ha : d271212 p = 1) (hb : d322190 p = 1) : d370083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46355 q = 1) (hb : d271212 q = 1) : d370072 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46355, d370072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104777 q ha hb
    | true =>
      simp only [d46355, d370072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104778 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322186 q = 1) : d370073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322186, d370073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322186, d370073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46427 q = 1) (hb : d271212 q = 1) : d370078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46427, d370078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104781 q ha hb
    | true =>
      simp only [d46427, d370078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46428 q = 1) (hb : d271212 q = 1) : d370079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46428, d370079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46428, d370079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322187 q = 1) : d370080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322187, d370080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322187, d370080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322188 q = 1) : d370081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322188, d370081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322188, d370081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d322189 q = 1) : d370082 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322189, d370082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322189, d370082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d322190 q = 1) : d370083 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322190, d370083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322190, d370083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104783 (p : Pattern) (ha : d271212 p = 1) (hb : d322196 p = 1) : d370100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46002 q = 1) (hb : d271212 q = 1) : d369896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46002, d369896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46002, d369896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104736 q ha hb
  have h2 (q : Pattern) (ha : d46003 q = 1) (hb : d271212 q = 1) : d369897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46003, d369897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46003, d369897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46012 q = 1) (hb : d271212 q = 1) : d369906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d369906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104736 q ha hb
    | true =>
      simp only [d46012, d369906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104739 q ha hb
  have h4 (q : Pattern) (ha : d46013 q = 1) (hb : d271212 q = 1) : d369907 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d369907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46013, d369907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46014 q = 1) (hb : d271212 q = 1) : d369908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46014, d369908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46014, d369908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322174 q = 1) : d369988 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322174, d369988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104763 q ha hb
    | true =>
      simp only [d322174, d369988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104770 q ha hb
  have h7 (q : Pattern) (ha : d46253 q = 1) (hb : d271212 q = 1) : d370001 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46253, d370001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104740 q ha hb
    | true =>
      simp only [d46253, d370001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104741 q ha hb
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d322175 q = 1) : d370002 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322175, d370002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322175, d370002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d322176 q = 1) : d370003 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322176, d370003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d322176, d370003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d322177 q = 1) : d370004 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322177, d370004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d322177, d370004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d322181 q = 1) : d370008 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322181, d370008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322181, d370008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104771 q ha hb
  have h12 (q : Pattern) (ha : d46262 q = 1) (hb : d271212 q = 1) : d370010 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46262, d370010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46262, d370010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104742 q ha hb
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d322182 q = 1) : d370011 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322182, d370011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d322182, d370011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d322183 q = 1) : d370012 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322183, d370012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322183, d370012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d322184 q = 1) : d370013 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322184, d370013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322184, d370013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d271212 q = 1) (hb : d322185 q = 1) : d370014 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322185, d370014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322185, d370014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d271212 q = 1) (hb : d322191 q = 1) : d370084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322191, d370084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322191, d370084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104782 q ha hb
  have h18 (q : Pattern) (ha : d46444 q = 1) (hb : d271212 q = 1) : d370095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46444, d370095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46444, d370095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104747 q ha hb
  have h19 (q : Pattern) (ha : d271212 q = 1) (hb : d322192 q = 1) : d370096 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322192, d370096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322192, d370096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d271212 q = 1) (hb : d322193 q = 1) : d370097 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322193, d370097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d322193, d370097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d271212 q = 1) (hb : d322194 q = 1) : d370098 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322194, d370098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d322194, d370098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d271212 q = 1) (hb : d322195 q = 1) : d370099 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322195, d370099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d322195, d370099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d271212 q = 1) (hb : d322196 q = 1) : d370100 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322196, d370100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322196, d370100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro104784 (p : Pattern) (ha : d271212 p = 1) (hb : d322202 p = 1) : d370106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d322197 q = 1) : d370101 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322197, d370101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322197, d370101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104783 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322198 q = 1) : d370102 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322198, d370102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322198, d370102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322199 q = 1) : d370103 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322199, d370103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322199, d370103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322200 q = 1) : d370104 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322200, d370104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322200, d370104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322201 q = 1) : d370105 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322201, d370105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322201, d370105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322202 q = 1) : d370106 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322202, d370106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322202, d370106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104785 (p : Pattern) (ha : d271212 p = 1) (hb : d322208 p = 1) : d370381 p = 1 := by
  have h0 (q : Pattern) (ha : d271212 q = 1) (hb : d322122 q = 1) : d369622 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d369622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104620 q ha hb
    | true =>
      simp only [d322122, d369622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104667 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322162 q = 1) : d369853 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322162, d369853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322162, d369853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104722 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322163 q = 1) : d369854 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d369854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d369854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322203 q = 1) : d370107 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322203, d370107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322203, d370107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104784 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322204 q = 1) : d370108 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322204, d370108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322204, d370108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322205 q = 1) : d370109 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d322205, d370109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322205, d370109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d321678 q = 1) : d370376 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321678, d370376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321678, d370376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104530 q ha hb
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d321679 q = 1) : d370377 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321679, d370377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321679, d370377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d321680 q = 1) : d370378 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321680, d370378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321680, d370378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d322206 q = 1) : d370379 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d322206, d370379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322206, d370379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d321721 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104580 q ha hb
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d321722 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d321723 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d321724 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d322207 q = 1) : d370380 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d322207, d370380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322207, d370380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d271212 q = 1) (hb : d322208 q = 1) : d370381 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d322208, d370381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322208, d370381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro104786 (p : Pattern) (ha : d271212 p = 1) (hb : d322214 p = 1) : d370387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d322209 q = 1) : d370382 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d322209, d370382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104785 q ha hb
    | true =>
      simp only [d322209, d370382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322210 q = 1) : d370383 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d322210, d370383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322210, d370383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322211 q = 1) : d370384 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d322211, d370384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322211, d370384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322212 q = 1) : d370385 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d322212, d370385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322212, d370385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322213 q = 1) : d370386 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d322213, d370386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322213, d370386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322214 q = 1) : d370387 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d322214, d370387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322214, d370387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104787 (p : Pattern) (ha : d271212 p = 1) (hb : d322220 p = 1) : d370393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d322215 q = 1) : d370388 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d322215, d370388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104786 q ha hb
    | true =>
      simp only [d322215, d370388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322216 q = 1) : d370389 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d322216, d370389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322216, d370389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322217 q = 1) : d370390 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d322217, d370390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322217, d370390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322218 q = 1) : d370391 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d322218, d370391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322218, d370391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322219 q = 1) : d370392 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d370392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322219, d370392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322220 q = 1) : d370393 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, d370393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322220, d370393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104788 (p : Pattern) (ha : d271212 p = 1) (hb : d322226 p = 1) : d370399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d322221 q = 1) : d370394 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, d370394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104787 q ha hb
    | true =>
      simp only [d322221, d370394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322222 q = 1) : d370395 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, d370395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, d370395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322223 q = 1) : d370396 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, d370396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, d370396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322224 q = 1) : d370397 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, d370397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, d370397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322225 q = 1) : d370398 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, d370398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, d370398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322226 q = 1) : d370399 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, d370399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, d370399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104789 (p : Pattern) (ha : d271212 p = 1) (hb : d322232 p = 1) : d370405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d322227 q = 1) : d370400 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, d370400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104788 q ha hb
    | true =>
      simp only [d322227, d370400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322228 q = 1) : d370401 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, d370401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, d370401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322229 q = 1) : d370402 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, d370402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, d370402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322230 q = 1) : d370403 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, d370403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, d370403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322231 q = 1) : d370404 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, d370404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, d370404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322232 q = 1) : d370405 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, d370405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, d370405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104790 (p : Pattern) (ha : d271212 p = 1) (hb : d322238 p = 1) : d370411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d322233 q = 1) : d370406 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, d370406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104789 q ha hb
    | true =>
      simp only [d322233, d370406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322234 q = 1) : d370407 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, d370407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, d370407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322235 q = 1) : d370408 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, d370408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, d370408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322236 q = 1) : d370409 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, d370409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, d370409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322237 q = 1) : d370410 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, d370410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, d370410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322238 q = 1) : d370411 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, d370411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, d370411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104791 (p : Pattern) (ha : d271212 p = 1) (hb : d322244 p = 1) : d370417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d322239 q = 1) : d370412 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, d370412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104790 q ha hb
    | true =>
      simp only [d322239, d370412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322240 q = 1) : d370413 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, d370413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, d370413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322241 q = 1) : d370414 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, d370414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, d370414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322242 q = 1) : d370415 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, d370415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, d370415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322243 q = 1) : d370416 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, d370416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, d370416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322244 q = 1) : d370417 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, d370417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, d370417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104792 (p : Pattern) (ha : d271212 p = 1) (hb : d322250 p = 1) : d370423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d322245 q = 1) : d370418 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, d370418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104791 q ha hb
    | true =>
      simp only [d322245, d370418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d322246 q = 1) : d370419 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, d370419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, d370419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d322247 q = 1) : d370420 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, d370420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, d370420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d322248 q = 1) : d370421 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, d370421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, d370421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d322249 q = 1) : d370422 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, d370422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, d370422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d322250 q = 1) : d370423 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, d370423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, d370423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104793 (p : Pattern) (ha : d46460 p = 1) (hb : d368770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52665 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1084 q = 1) (hb : d52665 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44996 q = 1) (hb : d52665 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46459 q = 1) (hb : d220155 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46459, d220155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46459, d220155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d46460 q = 1) (hb : d368770 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46460, d368770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46460, d368770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro104794 (p : Pattern) (ha : d368775 p = 1) (hb : d370114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d368771 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, d368771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46461, d368771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104793 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d368771 q = 1) (hb : d370110 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d368772 q = 1) (hb : d370111 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368772, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368772, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368773 q = 1) (hb : d370112 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368773, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368773, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368774 q = 1) (hb : d370113 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368774, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368774, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368775 q = 1) (hb : d370114 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368775, d370114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368775, d370114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro104795 (p : Pattern) (ha : d46473 p = 1) (hb : d219220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d45587 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46472 q = 1) (hb : d219219 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46472, d219219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46472, d219219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d46473 q = 1) (hb : d219220 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46473, d219220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46473, d219220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro104796 (p : Pattern) (ha : d368781 p = 1) (hb : d370120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d368771 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, d368771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46461, d368771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104793 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d368771 q = 1) (hb : d370110 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d368772 q = 1) (hb : d370111 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368772, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368772, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368773 q = 1) (hb : d370112 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368773, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368773, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368774 q = 1) (hb : d370113 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368774, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368774, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46474 q = 1) (hb : d220224 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, d220224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46474, d220224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104795 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d220224 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d220224 q = 1) (hb : d276467 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d276467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d276467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d220225 q = 1) (hb : d276487 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d220225, d276487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d220225, d276487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d46477 q = 1) (hb : d219221 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, d219221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104795 q ha hb
    | true =>
      simp only [d46477, d219221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d219221 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d179204 q = 1) (hb : d219221 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d219222 q = 1) (hb : d275501 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d219222, d275501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d219222, d275501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d220226 q = 1) (hb : d276488 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d220226, d276488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d220226, d276488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d220227 q = 1) (hb : d276489 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d220227, d276489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d220227, d276489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d368781 q = 1) (hb : d370120 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368781, d370120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368781, d370120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro104797 (p : Pattern) (ha : d368787 p = 1) (hb : d370126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368776 q = 1) (hb : d370115 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
    | true =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368777 q = 1) (hb : d370116 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368778 q = 1) (hb : d370117 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368778, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368778, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368779 q = 1) (hb : d370118 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368779, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368779, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368780 q = 1) (hb : d370119 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368780, d370119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368780, d370119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368782 q = 1) (hb : d370121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
    | true =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368783 q = 1) (hb : d370122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368784 q = 1) (hb : d370123 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368784, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368784, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d368785 q = 1) (hb : d370124 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368785, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368785, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d368786 q = 1) (hb : d370125 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368786, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368786, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368787 q = 1) (hb : d370126 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368787, d370126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368787, d370126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104798 (p : Pattern) (ha : d368789 p = 1) (hb : d370128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368776 q = 1) (hb : d370115 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
    | true =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368777 q = 1) (hb : d370116 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368778 q = 1) (hb : d370117 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368778, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368778, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368779 q = 1) (hb : d370118 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368779, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368779, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368782 q = 1) (hb : d370121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
    | true =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368783 q = 1) (hb : d370122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368784 q = 1) (hb : d370123 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368784, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368784, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368785 q = 1) (hb : d370124 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368785, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368785, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368786 q = 1) (hb : d370125 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368786, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368786, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368788 q = 1) (hb : d370127 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368788, d370127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368788, d370127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d368789 q = 1) (hb : d370128 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368789, d370128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d368789, d370128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104799 (p : Pattern) (ha : d220228 p = 1) (hb : d276490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46474 q = 1) (hb : d220224 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, d220224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46474, d220224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104795 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d220224 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d220224 q = 1) (hb : d276467 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d276467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d276467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d220225 q = 1) (hb : d276487 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d220225, d276487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d220225, d276487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46477 q = 1) (hb : d219221 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, d219221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104795 q ha hb
    | true =>
      simp only [d46477, d219221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d219221 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d179204 q = 1) (hb : d219221 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d179204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d219222 q = 1) (hb : d275501 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d219222, d275501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d219222, d275501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d220226 q = 1) (hb : d276488 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d220226, d276488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d220226, d276488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d220227 q = 1) (hb : d276489 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d220227, d276489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d220227, d276489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d220228 q = 1) (hb : d276490 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d220228, d276490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d220228, d276490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro104800 (p : Pattern) (ha : d368793 p = 1) (hb : d370132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368782 q = 1) (hb : d370121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
    | true =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368783 q = 1) (hb : d370122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368784 q = 1) (hb : d370123 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368784, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368784, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368785 q = 1) (hb : d370124 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368785, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368785, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368788 q = 1) (hb : d370127 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368788, d370127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368788, d370127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d220229 q = 1) (hb : d276491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d220229, d276491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104799 q ha hb
    | true =>
      simp only [d220229, d276491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d220230 q = 1) (hb : d276492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d220230, d276492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d220230, d276492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d220231 q = 1) (hb : d276493 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d220231, d276493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d220231, d276493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d220232 q = 1) (hb : d276494 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d220232, d276494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d220232, d276494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d220233 q = 1) (hb : d276495 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d220233, d276495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d220233, d276495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d368793 q = 1) (hb : d370132 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368793, d370132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368793, d370132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104801 (p : Pattern) (ha : d368800 p = 1) (hb : d370139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368790 q = 1) (hb : d370129 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368790, d370129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104797 q ha hb
    | true =>
      simp only [d368790, d370129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104798 q ha hb
  have h2 (q : Pattern) (ha : d368791 q = 1) (hb : d370130 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368791, d370130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368791, d370130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368792 q = 1) (hb : d370131 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368792, d370131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368792, d370131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368794 q = 1) (hb : d370133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368794, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104798 q ha hb
    | true =>
      simp only [d368794, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104800 q ha hb
  have h5 (q : Pattern) (ha : d368795 q = 1) (hb : d370134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368795, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368795, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368796 q = 1) (hb : d370135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368796, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368796, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368797 q = 1) (hb : d370136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368797, d370136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368797, d370136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368798 q = 1) (hb : d370137 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368798, d370137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368798, d370137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368799 q = 1) (hb : d370138 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368799, d370138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368799, d370138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368800 q = 1) (hb : d370139 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368800, d370139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d368800, d370139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro104802 (p : Pattern) (ha : d368804 p = 1) (hb : d370143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368794 q = 1) (hb : d370133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368794, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104798 q ha hb
    | true =>
      simp only [d368794, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104800 q ha hb
  have h2 (q : Pattern) (ha : d368795 q = 1) (hb : d370134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368795, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368795, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368796 q = 1) (hb : d370135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368796, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368796, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368798 q = 1) (hb : d370137 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368798, d370137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368798, d370137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368803 q = 1) (hb : d370142 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368803, d370142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368803, d370142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368804 q = 1) (hb : d370143 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368804, d370143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368804, d370143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104803 (p : Pattern) (ha : d368810 p = 1) (hb : d370149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368801 q = 1) (hb : d370140 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104801 q ha hb
    | true =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368802 q = 1) (hb : d370141 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368807 q = 1) (hb : d370146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368808 q = 1) (hb : d370147 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368808, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368808, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368809 q = 1) (hb : d370148 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368809, d370148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368809, d370148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368810 q = 1) (hb : d370149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368810, d370149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368810, d370149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104804 (p : Pattern) (ha : d368814 p = 1) (hb : d370153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368811 q = 1) (hb : d370150 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368812 q = 1) (hb : d370151 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368812, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368812, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368813 q = 1) (hb : d370152 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368813, d370152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368813, d370152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368814 q = 1) (hb : d370153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368814, d370153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368814, d370153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104805 (p : Pattern) (ha : d368820 p = 1) (hb : d370159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368815 q = 1) (hb : d370154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104803 q ha hb
    | true =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104804 q ha hb
  have h2 (q : Pattern) (ha : d368816 q = 1) (hb : d370155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368816, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368816, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368817 q = 1) (hb : d370156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368817, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368817, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368818 q = 1) (hb : d370157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368818, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368818, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368819 q = 1) (hb : d370158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368819, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368819, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368820 q = 1) (hb : d370159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368820, d370159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368820, d370159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104806 (p : Pattern) (ha : d368823 p = 1) (hb : d370162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368801 q = 1) (hb : d370140 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104801 q ha hb
    | true =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368802 q = 1) (hb : d370141 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368807 q = 1) (hb : d370146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368808 q = 1) (hb : d370147 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368808, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368808, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368809 q = 1) (hb : d370148 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368809, d370148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368809, d370148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368823 q = 1) (hb : d370162 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368823, d370162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368823, d370162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104807 (p : Pattern) (ha : d368824 p = 1) (hb : d370163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368811 q = 1) (hb : d370150 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368812 q = 1) (hb : d370151 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368812, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368812, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368813 q = 1) (hb : d370152 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368813, d370152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368813, d370152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368824 q = 1) (hb : d370163 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368824, d370163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368824, d370163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104808 (p : Pattern) (ha : d368830 p = 1) (hb : d370169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368815 q = 1) (hb : d370154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104803 q ha hb
    | true =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104804 q ha hb
  have h2 (q : Pattern) (ha : d368816 q = 1) (hb : d370155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368816, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368816, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368817 q = 1) (hb : d370156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368817, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368817, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368818 q = 1) (hb : d370157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368818, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368818, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368819 q = 1) (hb : d370158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368819, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368819, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368825 q = 1) (hb : d370164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368825, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104806 q ha hb
    | true =>
      simp only [d368825, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104807 q ha hb
  have h7 (q : Pattern) (ha : d368826 q = 1) (hb : d370165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368826, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368826, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368827 q = 1) (hb : d370166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368827, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368827, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368828 q = 1) (hb : d370167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368828, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368828, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368829 q = 1) (hb : d370168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368829, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368829, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368830 q = 1) (hb : d370169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368830, d370169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368830, d370169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104809 (p : Pattern) (ha : d368835 p = 1) (hb : d370174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368801 q = 1) (hb : d370140 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104801 q ha hb
    | true =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368802 q = 1) (hb : d370141 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368807 q = 1) (hb : d370146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368808 q = 1) (hb : d370147 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368808, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368808, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368834 q = 1) (hb : d370173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368834, d370173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368834, d370173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368835 q = 1) (hb : d370174 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368835, d370174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368835, d370174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104810 (p : Pattern) (ha : d368837 p = 1) (hb : d370176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368811 q = 1) (hb : d370150 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368812 q = 1) (hb : d370151 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368812, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368812, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368836 q = 1) (hb : d370175 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368836, d370175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368836, d370175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368837 q = 1) (hb : d370176 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368837, d370176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368837, d370176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104811 (p : Pattern) (ha : d368844 p = 1) (hb : d370183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368801 q = 1) (hb : d370140 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104801 q ha hb
    | true =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368802 q = 1) (hb : d370141 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368807 q = 1) (hb : d370146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368842 q = 1) (hb : d370181 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368842, d370181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368842, d370181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368843 q = 1) (hb : d370182 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368843, d370182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368843, d370182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368844 q = 1) (hb : d370183 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368844, d370183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368844, d370183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104812 (p : Pattern) (ha : d368847 p = 1) (hb : d370186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368811 q = 1) (hb : d370150 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368845 q = 1) (hb : d370184 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368845, d370184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368845, d370184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368846 q = 1) (hb : d370185 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368846, d370185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368846, d370185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368847 q = 1) (hb : d370186 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368847, d370186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368847, d370186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104813 (p : Pattern) (ha : d368851 p = 1) (hb : d370190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368776 q = 1) (hb : d370115 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
    | true =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368777 q = 1) (hb : d370116 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368778 q = 1) (hb : d370117 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368778, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368778, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368779 q = 1) (hb : d370118 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368779, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368779, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368780 q = 1) (hb : d370119 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368780, d370119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368780, d370119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368851 q = 1) (hb : d370190 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368851, d370190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368851, d370190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104814 (p : Pattern) (ha : d368857 p = 1) (hb : d370196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368852 q = 1) (hb : d370191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368852, d370191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104813 q ha hb
    | true =>
      simp only [d368852, d370191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104797 q ha hb
  have h2 (q : Pattern) (ha : d368853 q = 1) (hb : d370192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368853, d370192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368853, d370192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368854 q = 1) (hb : d370193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368854, d370193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368854, d370193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368790 q = 1) (hb : d370129 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368790, d370129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104797 q ha hb
    | true =>
      simp only [d368790, d370129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104798 q ha hb
  have h5 (q : Pattern) (ha : d368791 q = 1) (hb : d370130 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368791, d370130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368791, d370130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368792 q = 1) (hb : d370131 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368792, d370131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368792, d370131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368855 q = 1) (hb : d370194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368855, d370194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368855, d370194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368794 q = 1) (hb : d370133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368794, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104798 q ha hb
    | true =>
      simp only [d368794, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104800 q ha hb
  have h9 (q : Pattern) (ha : d368795 q = 1) (hb : d370134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368795, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368795, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368796 q = 1) (hb : d370135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368796, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368796, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368797 q = 1) (hb : d370136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368797, d370136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368797, d370136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d368856 q = 1) (hb : d370195 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368856, d370195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368856, d370195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d368857 q = 1) (hb : d370196 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368857, d370196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d368857, d370196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro104815 (p : Pattern) (ha : d368863 p = 1) (hb : d370202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368858 q = 1) (hb : d370197 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368858, d370197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104814 q ha hb
    | true =>
      simp only [d368858, d370197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368859 q = 1) (hb : d370198 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368859, d370198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368859, d370198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368801 q = 1) (hb : d370140 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104801 q ha hb
    | true =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368802 q = 1) (hb : d370141 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368860 q = 1) (hb : d370199 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368860, d370199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368860, d370199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368861 q = 1) (hb : d370200 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368861, d370200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368861, d370200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368862 q = 1) (hb : d370201 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368862, d370201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368862, d370201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368863 q = 1) (hb : d370202 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368863, d370202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368863, d370202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104816 (p : Pattern) (ha : d368866 p = 1) (hb : d370205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d368771 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, d368771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46461, d368771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104793 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d368771 q = 1) (hb : d370110 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d370110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d368772 q = 1) (hb : d370111 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d368772, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368772, d370111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368773 q = 1) (hb : d370112 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d368773, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368773, d370112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368774 q = 1) (hb : d370113 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d368774, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368774, d370113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368866 q = 1) (hb : d370205 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d368866, d370205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368866, d370205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro104817 (p : Pattern) (ha : d368872 p = 1) (hb : d370211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368776 q = 1) (hb : d370115 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
    | true =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368777 q = 1) (hb : d370116 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368778 q = 1) (hb : d370117 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368778, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368778, d370117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368779 q = 1) (hb : d370118 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368779, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368779, d370118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368782 q = 1) (hb : d370121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
    | true =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368783 q = 1) (hb : d370122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368784 q = 1) (hb : d370123 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368784, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368784, d370123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368785 q = 1) (hb : d370124 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368785, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368785, d370124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368786 q = 1) (hb : d370125 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368786, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368786, d370125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368867 q = 1) (hb : d370206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368867, d370206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104816 q ha hb
    | true =>
      simp only [d368867, d370206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d368868 q = 1) (hb : d370207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368868, d370207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d368868, d370207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d368869 q = 1) (hb : d370208 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368869, d370208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368869, d370208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d368870 q = 1) (hb : d370209 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368870, d370209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d368870, d370209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d368871 q = 1) (hb : d370210 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368871, d370210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d368871, d370210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d368872 q = 1) (hb : d370211 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368872, d370211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d368872, d370211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104818 (p : Pattern) (ha : d368873 p = 1) (hb : d370212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368867 q = 1) (hb : d370206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368867, d370206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104816 q ha hb
    | true =>
      simp only [d368867, d370206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368868 q = 1) (hb : d370207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368868, d370207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368868, d370207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368869 q = 1) (hb : d370208 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368869, d370208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368869, d370208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368870 q = 1) (hb : d370209 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368870, d370209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368870, d370209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368871 q = 1) (hb : d370210 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368871, d370210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368871, d370210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368873 q = 1) (hb : d370212 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368873, d370212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368873, d370212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104819 (p : Pattern) (ha : d368879 p = 1) (hb : d370218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368790 q = 1) (hb : d370129 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368790, d370129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104797 q ha hb
    | true =>
      simp only [d368790, d370129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104798 q ha hb
  have h2 (q : Pattern) (ha : d368791 q = 1) (hb : d370130 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368791, d370130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368791, d370130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368792 q = 1) (hb : d370131 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368792, d370131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368792, d370131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368794 q = 1) (hb : d370133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368794, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104798 q ha hb
    | true =>
      simp only [d368794, d370133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104800 q ha hb
  have h5 (q : Pattern) (ha : d368795 q = 1) (hb : d370134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368795, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368795, d370134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368796 q = 1) (hb : d370135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368796, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368796, d370135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368797 q = 1) (hb : d370136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368797, d370136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368797, d370136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368874 q = 1) (hb : d370213 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368874, d370213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104817 q ha hb
    | true =>
      simp only [d368874, d370213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104818 q ha hb
  have h9 (q : Pattern) (ha : d368875 q = 1) (hb : d370214 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368875, d370214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368875, d370214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368876 q = 1) (hb : d370215 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368876, d370215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368876, d370215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368877 q = 1) (hb : d370216 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368877, d370216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d368877, d370216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d368878 q = 1) (hb : d370217 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368878, d370217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368878, d370217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d368879 q = 1) (hb : d370218 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368879, d370218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d368879, d370218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro104820 (p : Pattern) (ha : d368885 p = 1) (hb : d370224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368880 q = 1) (hb : d370219 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368880, d370219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104819 q ha hb
    | true =>
      simp only [d368880, d370219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368881 q = 1) (hb : d370220 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368881, d370220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368881, d370220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368882 q = 1) (hb : d370221 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368882, d370221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368882, d370221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368883 q = 1) (hb : d370222 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368883, d370222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368883, d370222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368884 q = 1) (hb : d370223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368884, d370223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368884, d370223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368885 q = 1) (hb : d370224 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368885, d370224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368885, d370224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104821 (p : Pattern) (ha : d368891 p = 1) (hb : d370230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368838 q = 1) (hb : d370177 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368838, d370177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104809 q ha hb
    | true =>
      simp only [d368838, d370177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104810 q ha hb
  have h2 (q : Pattern) (ha : d368839 q = 1) (hb : d370178 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368839, d370178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368839, d370178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368840 q = 1) (hb : d370179 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368840, d370179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368840, d370179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368841 q = 1) (hb : d370180 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368841, d370180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368841, d370180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368848 q = 1) (hb : d370187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368848, d370187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104811 q ha hb
    | true =>
      simp only [d368848, d370187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104812 q ha hb
  have h6 (q : Pattern) (ha : d368849 q = 1) (hb : d370188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368849, d370188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368849, d370188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368850 q = 1) (hb : d370189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368850, d370189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368850, d370189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368864 q = 1) (hb : d370203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368864, d370203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104815 q ha hb
    | true =>
      simp only [d368864, d370203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104803 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d368815 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d368865 q = 1) (hb : d370204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368865, d370204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368865, d370204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d368886 q = 1) (hb : d370225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368886, d370225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104820 q ha hb
    | true =>
      simp only [d368886, d370225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d368887 q = 1) (hb : d370226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368887, d370226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d368887, d370226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d368888 q = 1) (hb : d370227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368888, d370227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d368888, d370227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d368889 q = 1) (hb : d370228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368889, d370228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368889, d370228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d368890 q = 1) (hb : d370229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368890, d370229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368890, d370229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d368891 q = 1) (hb : d370230 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368891, d370230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368891, d370230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104822 (p : Pattern) (ha : d368892 p = 1) (hb : d370231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368801 q = 1) (hb : d370140 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104801 q ha hb
    | true =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368802 q = 1) (hb : d370141 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368807 q = 1) (hb : d370146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368808 q = 1) (hb : d370147 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368808, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368808, d370147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368834 q = 1) (hb : d370173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368834, d370173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368834, d370173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368892 q = 1) (hb : d370231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368892, d370231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368892, d370231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104823 (p : Pattern) (ha : d368893 p = 1) (hb : d370232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368811 q = 1) (hb : d370150 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368812 q = 1) (hb : d370151 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368812, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368812, d370151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368836 q = 1) (hb : d370175 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368836, d370175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368836, d370175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368893 q = 1) (hb : d370232 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368893, d370232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368893, d370232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104824 (p : Pattern) (ha : d368898 p = 1) (hb : d370237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368801 q = 1) (hb : d370140 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104801 q ha hb
    | true =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368802 q = 1) (hb : d370141 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368807 q = 1) (hb : d370146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368807, d370146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368842 q = 1) (hb : d370181 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368842, d370181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368842, d370181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368843 q = 1) (hb : d370182 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368843, d370182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368843, d370182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368898 q = 1) (hb : d370237 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368898, d370237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368898, d370237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104825 (p : Pattern) (ha : d368899 p = 1) (hb : d370238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368805 q = 1) (hb : d370144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104802 q ha hb
    | true =>
      simp only [d368805, d370144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368806 q = 1) (hb : d370145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368806, d370145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368811 q = 1) (hb : d370150 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368811, d370150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368845 q = 1) (hb : d370184 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368845, d370184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368845, d370184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368846 q = 1) (hb : d370185 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368846, d370185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368846, d370185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368899 q = 1) (hb : d370238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368899, d370238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368899, d370238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104826 (p : Pattern) (ha : d368903 p = 1) (hb : d370242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368858 q = 1) (hb : d370197 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368858, d370197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104814 q ha hb
    | true =>
      simp only [d368858, d370197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368859 q = 1) (hb : d370198 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368859, d370198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368859, d370198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368801 q = 1) (hb : d370140 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104801 q ha hb
    | true =>
      simp only [d368801, d370140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368802 q = 1) (hb : d370141 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368802, d370141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368860 q = 1) (hb : d370199 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368860, d370199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368860, d370199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368861 q = 1) (hb : d370200 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368861, d370200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368861, d370200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368862 q = 1) (hb : d370201 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368862, d370201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368862, d370201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368903 q = 1) (hb : d370242 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368903, d370242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368903, d370242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104827 (p : Pattern) (ha : d368906 p = 1) (hb : d370245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368880 q = 1) (hb : d370219 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368880, d370219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104819 q ha hb
    | true =>
      simp only [d368880, d370219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368881 q = 1) (hb : d370220 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368881, d370220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368881, d370220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368882 q = 1) (hb : d370221 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368882, d370221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368882, d370221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368883 q = 1) (hb : d370222 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368883, d370222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368883, d370222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368884 q = 1) (hb : d370223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368884, d370223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368884, d370223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368906 q = 1) (hb : d370245 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368906, d370245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368906, d370245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104828 (p : Pattern) (ha : d368912 p = 1) (hb : d370251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368838 q = 1) (hb : d370177 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368838, d370177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104809 q ha hb
    | true =>
      simp only [d368838, d370177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104810 q ha hb
  have h2 (q : Pattern) (ha : d368839 q = 1) (hb : d370178 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368839, d370178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368839, d370178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368840 q = 1) (hb : d370179 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368840, d370179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368840, d370179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368841 q = 1) (hb : d370180 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368841, d370180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368841, d370180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368848 q = 1) (hb : d370187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368848, d370187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104811 q ha hb
    | true =>
      simp only [d368848, d370187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104812 q ha hb
  have h6 (q : Pattern) (ha : d368849 q = 1) (hb : d370188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368849, d370188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368849, d370188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368850 q = 1) (hb : d370189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368850, d370189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368850, d370189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368864 q = 1) (hb : d370203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368864, d370203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104815 q ha hb
    | true =>
      simp only [d368864, d370203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104803 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d368815 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d368865 q = 1) (hb : d370204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368865, d370204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368865, d370204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d368886 q = 1) (hb : d370225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368886, d370225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104820 q ha hb
    | true =>
      simp only [d368886, d370225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d368887 q = 1) (hb : d370226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368887, d370226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d368887, d370226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d368888 q = 1) (hb : d370227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368888, d370227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d368888, d370227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d368889 q = 1) (hb : d370228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368889, d370228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368889, d370228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d368890 q = 1) (hb : d370229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368890, d370229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368890, d370229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d368894 q = 1) (hb : d370233 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368894, d370233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104822 q ha hb
    | true =>
      simp only [d368894, d370233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104823 q ha hb
  have h17 (q : Pattern) (ha : d368895 q = 1) (hb : d370234 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368895, d370234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368895, d370234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d368896 q = 1) (hb : d370235 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368896, d370235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d368896, d370235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d368897 q = 1) (hb : d370236 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368897, d370236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368897, d370236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d368900 q = 1) (hb : d370239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368900, d370239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104824 q ha hb
    | true =>
      simp only [d368900, d370239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104825 q ha hb
  have h21 (q : Pattern) (ha : d368901 q = 1) (hb : d370240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368901, d370240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368901, d370240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d368902 q = 1) (hb : d370241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368902, d370241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d368902, d370241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d368904 q = 1) (hb : d370243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368904, d370243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104826 q ha hb
    | true =>
      simp only [d368904, d370243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104806 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d368825 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d368905 q = 1) (hb : d370244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368905, d370244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d368905, d370244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d368907 q = 1) (hb : d370246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368907, d370246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104827 q ha hb
    | true =>
      simp only [d368907, d370246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d368908 q = 1) (hb : d370247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368908, d370247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d368908, d370247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d368909 q = 1) (hb : d370248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368909, d370248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d368909, d370248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d368910 q = 1) (hb : d370249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368910, d370249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d368910, d370249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d368911 q = 1) (hb : d370250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368911, d370250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d368911, d370250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d368912 q = 1) (hb : d370251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368912, d370251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d368912, d370251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro104829 (p : Pattern) (ha : d368919 p = 1) (hb : d370258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368815 q = 1) (hb : d370154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104803 q ha hb
    | true =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104804 q ha hb
  have h2 (q : Pattern) (ha : d368816 q = 1) (hb : d370155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368816, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368816, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368817 q = 1) (hb : d370156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368817, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368817, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368818 q = 1) (hb : d370157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368818, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368818, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368819 q = 1) (hb : d370158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368819, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368819, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368914 q = 1) (hb : d370253 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368914, d370253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104804 q ha hb
    | true =>
      simp only [d368914, d370253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368915 q = 1) (hb : d370254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368915, d370254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368915, d370254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368916 q = 1) (hb : d370255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368916, d370255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368916, d370255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368917 q = 1) (hb : d370256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368917, d370256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368917, d370256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368918 q = 1) (hb : d370257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368918, d370257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368918, d370257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368919 q = 1) (hb : d370258 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368919, d370258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368919, d370258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104830 (p : Pattern) (ha : d368925 p = 1) (hb : d370264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368914 q = 1) (hb : d370253 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368914, d370253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104804 q ha hb
    | true =>
      simp only [d368914, d370253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368915 q = 1) (hb : d370254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368915, d370254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368915, d370254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368916 q = 1) (hb : d370255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368916, d370255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368916, d370255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368917 q = 1) (hb : d370256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368917, d370256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368917, d370256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368918 q = 1) (hb : d370257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368918, d370257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368918, d370257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368920 q = 1) (hb : d370259 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368920, d370259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104807 q ha hb
    | true =>
      simp only [d368920, d370259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368921 q = 1) (hb : d370260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368921, d370260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368921, d370260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368922 q = 1) (hb : d370261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368922, d370261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368922, d370261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368923 q = 1) (hb : d370262 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368923, d370262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368923, d370262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368924 q = 1) (hb : d370263 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368924, d370263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368924, d370263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368925 q = 1) (hb : d370264 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368925, d370264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368925, d370264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104831 (p : Pattern) (ha : d368932 p = 1) (hb : d370271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368904 q = 1) (hb : d370243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368904, d370243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104826 q ha hb
    | true =>
      simp only [d368904, d370243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104806 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368825 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d368905 q = 1) (hb : d370244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368905, d370244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368905, d370244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d368907 q = 1) (hb : d370246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368907, d370246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104827 q ha hb
    | true =>
      simp only [d368907, d370246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368908 q = 1) (hb : d370247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368908, d370247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368908, d370247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368909 q = 1) (hb : d370248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368909, d370248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368909, d370248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368930 q = 1) (hb : d370269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368930, d370269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368930, d370269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368931 q = 1) (hb : d370270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368931, d370270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368931, d370270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d368932 q = 1) (hb : d370271 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368932, d370271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368932, d370271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104832 (p : Pattern) (ha : d368934 p = 1) (hb : d370273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368920 q = 1) (hb : d370259 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368920, d370259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104807 q ha hb
    | true =>
      simp only [d368920, d370259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368921 q = 1) (hb : d370260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368921, d370260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368921, d370260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368922 q = 1) (hb : d370261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368922, d370261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368922, d370261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368923 q = 1) (hb : d370262 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368923, d370262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368923, d370262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368924 q = 1) (hb : d370263 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368924, d370263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368924, d370263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368934 q = 1) (hb : d370273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368934, d370273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368934, d370273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104833 (p : Pattern) (ha : d368945 p = 1) (hb : d370284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368940 q = 1) (hb : d370279 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368940, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368940, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
  have h2 (q : Pattern) (ha : d368776 q = 1) (hb : d370115 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
    | true =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368941 q = 1) (hb : d370280 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368941, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368941, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368777 q = 1) (hb : d370116 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368942 q = 1) (hb : d370281 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368942, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368942, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368943 q = 1) (hb : d370282 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368943, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368943, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368944 q = 1) (hb : d370283 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368944, d370283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368944, d370283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368945 q = 1) (hb : d370284 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368945, d370284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368945, d370284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104834 (p : Pattern) (ha : d368951 p = 1) (hb : d370290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368940 q = 1) (hb : d370279 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368940, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368940, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
  have h2 (q : Pattern) (ha : d368776 q = 1) (hb : d370115 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
    | true =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368941 q = 1) (hb : d370280 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368941, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368941, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368777 q = 1) (hb : d370116 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368942 q = 1) (hb : d370281 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368942, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368942, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368943 q = 1) (hb : d370282 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368943, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368943, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368944 q = 1) (hb : d370283 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368944, d370283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368944, d370283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368946 q = 1) (hb : d370285 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368946, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368946, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
  have h9 (q : Pattern) (ha : d368782 q = 1) (hb : d370121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
    | true =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d368947 q = 1) (hb : d370286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368947, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368947, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368783 q = 1) (hb : d370122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d368948 q = 1) (hb : d370287 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368948, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d368948, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d368949 q = 1) (hb : d370288 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368949, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d368949, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d368950 q = 1) (hb : d370289 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368950, d370289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368950, d370289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d368951 q = 1) (hb : d370290 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368951, d370290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368951, d370290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104835 (p : Pattern) (ha : d368956 p = 1) (hb : d370295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368940 q = 1) (hb : d370279 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368940, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368940, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
  have h2 (q : Pattern) (ha : d368776 q = 1) (hb : d370115 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
    | true =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368941 q = 1) (hb : d370280 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368941, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368941, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368777 q = 1) (hb : d370116 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368942 q = 1) (hb : d370281 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368942, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368942, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368943 q = 1) (hb : d370282 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368943, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368943, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368946 q = 1) (hb : d370285 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368946, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368946, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
  have h8 (q : Pattern) (ha : d368782 q = 1) (hb : d370121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
    | true =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368947 q = 1) (hb : d370286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368947, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368947, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368783 q = 1) (hb : d370122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d368948 q = 1) (hb : d370287 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368948, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d368948, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d368949 q = 1) (hb : d370288 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368949, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d368949, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d368950 q = 1) (hb : d370289 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368950, d370289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368950, d370289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d368955 q = 1) (hb : d370294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368955, d370294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d368955, d370294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d368956 q = 1) (hb : d370295 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368956, d370295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d368956, d370295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104836 (p : Pattern) (ha : d368961 p = 1) (hb : d370300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368946 q = 1) (hb : d370285 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368946, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368946, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
  have h2 (q : Pattern) (ha : d368782 q = 1) (hb : d370121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
    | true =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368947 q = 1) (hb : d370286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368947, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368947, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368783 q = 1) (hb : d370122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368948 q = 1) (hb : d370287 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368948, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368948, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368949 q = 1) (hb : d370288 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368949, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368949, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368955 q = 1) (hb : d370294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368955, d370294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368955, d370294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d220485 q = 1) (hb : d276731 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d220485, d276731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d220485, d276731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104799 q ha hb
  have h9 (q : Pattern) (ha : d220229 q = 1) (hb : d276491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d220229, d276491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104799 q ha hb
    | true =>
      simp only [d220229, d276491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d220486 q = 1) (hb : d276732 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d220486, d276732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d220486, d276732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d220230 q = 1) (hb : d276492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d220230, d276492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d220230, d276492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d220487 q = 1) (hb : d276733 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d220487, d276733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d220487, d276733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d220488 q = 1) (hb : d276734 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d220488, d276734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d220488, d276734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d220489 q = 1) (hb : d276735 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d220489, d276735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d220489, d276735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d368961 q = 1) (hb : d370300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368961, d370300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368961, d370300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104837 (p : Pattern) (ha : d368967 p = 1) (hb : d370306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368952 q = 1) (hb : d370291 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368952, d370291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104833 q ha hb
    | true =>
      simp only [d368952, d370291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104834 q ha hb
  have h2 (q : Pattern) (ha : d368953 q = 1) (hb : d370292 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368953, d370292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368953, d370292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368954 q = 1) (hb : d370293 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368954, d370293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368954, d370293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368957 q = 1) (hb : d370296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368957, d370296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104834 q ha hb
    | true =>
      simp only [d368957, d370296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104835 q ha hb
  have h5 (q : Pattern) (ha : d368958 q = 1) (hb : d370297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368958, d370297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368958, d370297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368959 q = 1) (hb : d370298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368959, d370298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368959, d370298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368960 q = 1) (hb : d370299 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368960, d370299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368960, d370299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368962 q = 1) (hb : d370301 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368962, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104835 q ha hb
    | true =>
      simp only [d368962, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104836 q ha hb
  have h9 (q : Pattern) (ha : d368963 q = 1) (hb : d370302 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368963, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368963, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368964 q = 1) (hb : d370303 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368964, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368964, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368965 q = 1) (hb : d370304 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368965, d370304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368965, d370304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d368966 q = 1) (hb : d370305 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368966, d370305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368966, d370305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d368967 q = 1) (hb : d370306 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368967, d370306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d368967, d370306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro104838 (p : Pattern) (ha : d368972 p = 1) (hb : d370311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368957 q = 1) (hb : d370296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368957, d370296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104834 q ha hb
    | true =>
      simp only [d368957, d370296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104835 q ha hb
  have h2 (q : Pattern) (ha : d368958 q = 1) (hb : d370297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368958, d370297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368958, d370297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368959 q = 1) (hb : d370298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368959, d370298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368959, d370298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368962 q = 1) (hb : d370301 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368962, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104835 q ha hb
    | true =>
      simp only [d368962, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104836 q ha hb
  have h5 (q : Pattern) (ha : d368963 q = 1) (hb : d370302 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368963, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368963, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368964 q = 1) (hb : d370303 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368964, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368964, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368965 q = 1) (hb : d370304 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368965, d370304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368965, d370304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368970 q = 1) (hb : d370309 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368970, d370309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368970, d370309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368971 q = 1) (hb : d370310 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368971, d370310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368971, d370310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368972 q = 1) (hb : d370311 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368972, d370311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d368972, d370311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro104839 (p : Pattern) (ha : d368978 p = 1) (hb : d370317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368968 q = 1) (hb : d370307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368968, d370307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104837 q ha hb
    | true =>
      simp only [d368968, d370307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368969 q = 1) (hb : d370308 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368969, d370308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368969, d370308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368973 q = 1) (hb : d370312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368973, d370312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104838 q ha hb
    | true =>
      simp only [d368973, d370312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368974 q = 1) (hb : d370313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368974, d370313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368974, d370313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368975 q = 1) (hb : d370314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368975, d370314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368975, d370314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368976 q = 1) (hb : d370315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368976, d370315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368976, d370315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368977 q = 1) (hb : d370316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368977, d370316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368977, d370316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368978 q = 1) (hb : d370317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368978, d370317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368978, d370317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104840 (p : Pattern) (ha : d368980 p = 1) (hb : d370319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368962 q = 1) (hb : d370301 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368962, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104835 q ha hb
    | true =>
      simp only [d368962, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104836 q ha hb
  have h2 (q : Pattern) (ha : d368963 q = 1) (hb : d370302 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368963, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368963, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368964 q = 1) (hb : d370303 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368964, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368964, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368970 q = 1) (hb : d370309 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368970, d370309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368970, d370309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368979 q = 1) (hb : d370318 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d368979, d370318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368979, d370318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368980 q = 1) (hb : d370319 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d368980, d370319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368980, d370319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104841 (p : Pattern) (ha : d368986 p = 1) (hb : d370325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368973 q = 1) (hb : d370312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368973, d370312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104838 q ha hb
    | true =>
      simp only [d368973, d370312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368974 q = 1) (hb : d370313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368974, d370313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368974, d370313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368981 q = 1) (hb : d370320 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368981, d370320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104840 q ha hb
    | true =>
      simp only [d368981, d370320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368982 q = 1) (hb : d370321 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368982, d370321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368982, d370321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d368983 q = 1) (hb : d370322 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368983, d370322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368983, d370322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368984 q = 1) (hb : d370323 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368984, d370323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368984, d370323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368985 q = 1) (hb : d370324 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368985, d370324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368985, d370324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d368986 q = 1) (hb : d370325 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368986, d370325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368986, d370325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104842 (p : Pattern) (ha : d368999 p = 1) (hb : d370333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368940 q = 1) (hb : d370279 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368940, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368940, d370279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
  have h2 (q : Pattern) (ha : d368776 q = 1) (hb : d370115 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104794 q ha hb
    | true =>
      simp only [d368776, d370115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368941 q = 1) (hb : d370280 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368941, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368941, d370280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368777 q = 1) (hb : d370116 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368777, d370116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368942 q = 1) (hb : d370281 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368942, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368942, d370281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368943 q = 1) (hb : d370282 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368943, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368943, d370282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368946 q = 1) (hb : d370285 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368946, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368946, d370285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
  have h8 (q : Pattern) (ha : d368782 q = 1) (hb : d370121 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104796 q ha hb
    | true =>
      simp only [d368782, d370121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d368947 q = 1) (hb : d370286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368947, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368947, d370286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368783 q = 1) (hb : d370122 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368783, d370122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d368948 q = 1) (hb : d370287 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368948, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d368948, d370287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d368949 q = 1) (hb : d370288 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368949, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d368949, d370288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d368950 q = 1) (hb : d370289 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368950, d370289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368950, d370289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d368994 q = 1) (hb : d370328 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368994, d370328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368994, d370328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104816 q ha hb
  have h15 (q : Pattern) (ha : d368867 q = 1) (hb : d370206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368867, d370206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104816 q ha hb
    | true =>
      simp only [d368867, d370206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d368995 q = 1) (hb : d370329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368995, d370329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d368995, d370329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d368868 q = 1) (hb : d370207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368868, d370207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d368868, d370207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d368996 q = 1) (hb : d370330 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368996, d370330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d368996, d370330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d368997 q = 1) (hb : d370331 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368997, d370331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d368997, d370331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d368998 q = 1) (hb : d370332 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368998, d370332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d368998, d370332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d368999 q = 1) (hb : d370333 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d368999, d370333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d368999, d370333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro104843 (p : Pattern) (ha : d369000 p = 1) (hb : d370334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368994 q = 1) (hb : d370328 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368994, d370328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368994, d370328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104816 q ha hb
  have h2 (q : Pattern) (ha : d368867 q = 1) (hb : d370206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d368867, d370206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104816 q ha hb
    | true =>
      simp only [d368867, d370206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368995 q = 1) (hb : d370329 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368995, d370329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368995, d370329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368868 q = 1) (hb : d370207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d368868, d370207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368868, d370207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368996 q = 1) (hb : d370330 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d368996, d370330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368996, d370330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368997 q = 1) (hb : d370331 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d368997, d370331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368997, d370331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d368998 q = 1) (hb : d370332 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d368998, d370332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368998, d370332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d369000 q = 1) (hb : d370334 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d369000, d370334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d369000, d370334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro104844 (p : Pattern) (ha : d369006 p = 1) (hb : d370340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368957 q = 1) (hb : d370296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368957, d370296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104834 q ha hb
    | true =>
      simp only [d368957, d370296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104835 q ha hb
  have h2 (q : Pattern) (ha : d368958 q = 1) (hb : d370297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368958, d370297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368958, d370297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368959 q = 1) (hb : d370298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368959, d370298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368959, d370298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d368962 q = 1) (hb : d370301 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d368962, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104835 q ha hb
    | true =>
      simp only [d368962, d370301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104836 q ha hb
  have h5 (q : Pattern) (ha : d368963 q = 1) (hb : d370302 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d368963, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368963, d370302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368964 q = 1) (hb : d370303 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d368964, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368964, d370303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368965 q = 1) (hb : d370304 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d368965, d370304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368965, d370304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d369001 q = 1) (hb : d370335 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d369001, d370335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104842 q ha hb
    | true =>
      simp only [d369001, d370335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104843 q ha hb
  have h9 (q : Pattern) (ha : d369002 q = 1) (hb : d370336 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d369002, d370336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369002, d370336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d369003 q = 1) (hb : d370337 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d369003, d370337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369003, d370337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d369004 q = 1) (hb : d370338 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d369004, d370338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d369004, d370338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d369005 q = 1) (hb : d370339 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d369005, d370339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d369005, d370339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d369006 q = 1) (hb : d370340 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d369006, d370340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d369006, d370340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro104845 (p : Pattern) (ha : d369012 p = 1) (hb : d370346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369007 q = 1) (hb : d370341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d369007, d370341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104844 q ha hb
    | true =>
      simp only [d369007, d370341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369008 q = 1) (hb : d370342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d369008, d370342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369008, d370342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d369009 q = 1) (hb : d370343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d369009, d370343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369009, d370343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369010 q = 1) (hb : d370344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d369010, d370344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369010, d370344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369011 q = 1) (hb : d370345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d369011, d370345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369011, d370345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369012 q = 1) (hb : d370346 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d369012, d370346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369012, d370346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104846 (p : Pattern) (ha : d369018 p = 1) (hb : d370352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368987 q = 1) (hb : d370326 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368987, d370326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104839 q ha hb
    | true =>
      simp only [d368987, d370326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104841 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368992 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d368993 q = 1) (hb : d370327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368993, d370327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368993, d370327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d369013 q = 1) (hb : d370347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d369013, d370347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104845 q ha hb
    | true =>
      simp only [d369013, d370347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369014 q = 1) (hb : d370348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369014, d370348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369014, d370348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369015 q = 1) (hb : d370349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d369015, d370349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369015, d370349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d369016 q = 1) (hb : d370350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d369016, d370350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369016, d370350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d369017 q = 1) (hb : d370351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d369017, d370351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369017, d370351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d369018 q = 1) (hb : d370352 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d369018, d370352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369018, d370352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104847 (p : Pattern) (ha : d368991 p = 1) (hb : d370357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368981 q = 1) (hb : d370320 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d368981, d370320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104840 q ha hb
    | true =>
      simp only [d368981, d370320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d368982 q = 1) (hb : d370321 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d368982, d370321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368982, d370321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d368988 q = 1) (hb : d370354 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d368988, d370354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368988, d370354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d368989 q = 1) (hb : d370355 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d368989, d370355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368989, d370355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368990 q = 1) (hb : d370356 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d368990, d370356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368990, d370356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d368991 q = 1) (hb : d370357 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d368991, d370357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368991, d370357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104848 (p : Pattern) (ha : d369025 p = 1) (hb : d370363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369020 q = 1) (hb : d370358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d369020, d370358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104847 q ha hb
    | true =>
      simp only [d369020, d370358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369021 q = 1) (hb : d370359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369021, d370359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369021, d370359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d369022 q = 1) (hb : d370360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d369022, d370360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369022, d370360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369023 q = 1) (hb : d370361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d369023, d370361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369023, d370361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d369024 q = 1) (hb : d370362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d369024, d370362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369024, d370362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d369025 q = 1) (hb : d370363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d369025, d370363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369025, d370363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104849 (p : Pattern) (ha : d369031 p = 1) (hb : d370369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368821 q = 1) (hb : d370160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368821, d370160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368821, d370160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104805 q ha hb
  have h2 (q : Pattern) (ha : d368822 q = 1) (hb : d370161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368822, d370161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368822, d370161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d368831 q = 1) (hb : d370170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368831, d370170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104805 q ha hb
    | true =>
      simp only [d368831, d370170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104808 q ha hb
  have h4 (q : Pattern) (ha : d368832 q = 1) (hb : d370171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368832, d370171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368832, d370171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d368833 q = 1) (hb : d370172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368833, d370172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d368833, d370172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d368913 q = 1) (hb : d370252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368913, d370252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104821 q ha hb
    | true =>
      simp only [d368913, d370252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104828 q ha hb
  have h7 (q : Pattern) (ha : d368926 q = 1) (hb : d370265 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368926, d370265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104829 q ha hb
    | true =>
      simp only [d368926, d370265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104830 q ha hb
  have h8 (q : Pattern) (ha : d368927 q = 1) (hb : d370266 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368927, d370266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368927, d370266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d368928 q = 1) (hb : d370267 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368928, d370267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368928, d370267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d368929 q = 1) (hb : d370268 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368929, d370268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368929, d370268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d368933 q = 1) (hb : d370272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368933, d370272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368933, d370272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104831 q ha hb
  have h12 (q : Pattern) (ha : d368935 q = 1) (hb : d370274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368935, d370274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368935, d370274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104832 q ha hb
  have h13 (q : Pattern) (ha : d368936 q = 1) (hb : d370275 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368936, d370275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d368936, d370275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d368937 q = 1) (hb : d370276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368937, d370276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d368937, d370276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d368938 q = 1) (hb : d370277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368938, d370277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d368938, d370277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d368939 q = 1) (hb : d370278 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368939, d370278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d368939, d370278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d369019 q = 1) (hb : d370353 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d369019, d370353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369019, d370353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104846 q ha hb
  have h18 (q : Pattern) (ha : d369026 q = 1) (hb : d370364 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d369026, d370364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369026, d370364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104848 q ha hb
  have h19 (q : Pattern) (ha : d369027 q = 1) (hb : d370365 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d369027, d370365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d369027, d370365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d369028 q = 1) (hb : d370366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d369028, d370366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d369028, d370366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d369029 q = 1) (hb : d370367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d369029, d370367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d369029, d370367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d369030 q = 1) (hb : d370368 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d369030, d370368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d369030, d370368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d369031 q = 1) (hb : d370369 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d369031, d370369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d369031, d370369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro104850 (p : Pattern) (ha : d369037 p = 1) (hb : d370375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369032 q = 1) (hb : d370370 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d369032, d370370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369032, d370370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104849 q ha hb
  have h2 (q : Pattern) (ha : d369033 q = 1) (hb : d370371 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d369033, d370371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369033, d370371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d369034 q = 1) (hb : d370372 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d369034, d370372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369034, d370372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d369035 q = 1) (hb : d370373 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d369035, d370373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369035, d370373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d369036 q = 1) (hb : d370374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d369036, d370374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369036, d370374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d369037 q = 1) (hb : d370375 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d369037, d370375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369037, d370375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104851 (p : Pattern) (ha : d369341 p = 1) (hb : d370381 p = 1) : d370426 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d370109 q = 1) : d370109 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d369038 q = 1) (hb : d370376 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d369038, d370376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d369038, d370376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104850 q ha hb
  have h3 (q : Pattern) (ha : d369039 q = 1) (hb : d370377 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d369039, d370377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d369039, d370377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d369040 q = 1) (hb : d370378 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d369040, d370378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d369040, d370378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d369041 q = 1) (hb : d370379 q = 1) : d370424 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d369041, d370379, d370424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d369041, d370379, d370424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d369339 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d369340 q = 1) (hb : d370380 q = 1) : d370425 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d369340, d370380, d370425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369340, d370380, d370425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d369341 q = 1) (hb : d370381 q = 1) : d370426 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d369341, d370381, d370426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d369341, d370381, d370426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro104852 (p : Pattern) (ha : d369347 p = 1) (hb : d370387 p = 1) : d370432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369342 q = 1) (hb : d370382 q = 1) : d370427 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d369342, d370382, d370427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104851 q ha hb
    | true =>
      simp only [d369342, d370382, d370427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369343 q = 1) (hb : d370383 q = 1) : d370428 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d369343, d370383, d370428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369343, d370383, d370428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369344 q = 1) (hb : d370384 q = 1) : d370429 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d369344, d370384, d370429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369344, d370384, d370429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369345 q = 1) (hb : d370385 q = 1) : d370430 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d369345, d370385, d370430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369345, d370385, d370430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369346 q = 1) (hb : d370386 q = 1) : d370431 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d369346, d370386, d370431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369346, d370386, d370431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369347 q = 1) (hb : d370387 q = 1) : d370432 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d369347, d370387, d370432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369347, d370387, d370432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104853 (p : Pattern) (ha : d369353 p = 1) (hb : d370393 p = 1) : d370438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369348 q = 1) (hb : d370388 q = 1) : d370433 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d369348, d370388, d370433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104852 q ha hb
    | true =>
      simp only [d369348, d370388, d370433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369349 q = 1) (hb : d370389 q = 1) : d370434 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d369349, d370389, d370434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369349, d370389, d370434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369350 q = 1) (hb : d370390 q = 1) : d370435 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d369350, d370390, d370435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369350, d370390, d370435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369351 q = 1) (hb : d370391 q = 1) : d370436 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d369351, d370391, d370436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369351, d370391, d370436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369352 q = 1) (hb : d370392 q = 1) : d370437 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d369352, d370392, d370437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369352, d370392, d370437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369353 q = 1) (hb : d370393 q = 1) : d370438 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d369353, d370393, d370438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369353, d370393, d370438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104854 (p : Pattern) (ha : d369359 p = 1) (hb : d370399 p = 1) : d370444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369354 q = 1) (hb : d370394 q = 1) : d370439 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d369354, d370394, d370439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104853 q ha hb
    | true =>
      simp only [d369354, d370394, d370439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369355 q = 1) (hb : d370395 q = 1) : d370440 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d369355, d370395, d370440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369355, d370395, d370440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369356 q = 1) (hb : d370396 q = 1) : d370441 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d369356, d370396, d370441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369356, d370396, d370441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369357 q = 1) (hb : d370397 q = 1) : d370442 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d369357, d370397, d370442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369357, d370397, d370442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369358 q = 1) (hb : d370398 q = 1) : d370443 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d369358, d370398, d370443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369358, d370398, d370443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369359 q = 1) (hb : d370399 q = 1) : d370444 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d369359, d370399, d370444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369359, d370399, d370444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104855 (p : Pattern) (ha : d369365 p = 1) (hb : d370405 p = 1) : d370450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369360 q = 1) (hb : d370400 q = 1) : d370445 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d369360, d370400, d370445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104854 q ha hb
    | true =>
      simp only [d369360, d370400, d370445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369361 q = 1) (hb : d370401 q = 1) : d370446 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d369361, d370401, d370446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369361, d370401, d370446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369362 q = 1) (hb : d370402 q = 1) : d370447 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d369362, d370402, d370447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369362, d370402, d370447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369363 q = 1) (hb : d370403 q = 1) : d370448 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d369363, d370403, d370448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369363, d370403, d370448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369364 q = 1) (hb : d370404 q = 1) : d370449 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d369364, d370404, d370449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369364, d370404, d370449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369365 q = 1) (hb : d370405 q = 1) : d370450 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d369365, d370405, d370450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369365, d370405, d370450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104856 (p : Pattern) (ha : d369371 p = 1) (hb : d370411 p = 1) : d370456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369366 q = 1) (hb : d370406 q = 1) : d370451 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d369366, d370406, d370451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104855 q ha hb
    | true =>
      simp only [d369366, d370406, d370451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369367 q = 1) (hb : d370407 q = 1) : d370452 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d369367, d370407, d370452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369367, d370407, d370452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369368 q = 1) (hb : d370408 q = 1) : d370453 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d369368, d370408, d370453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369368, d370408, d370453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369369 q = 1) (hb : d370409 q = 1) : d370454 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d369369, d370409, d370454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369369, d370409, d370454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369370 q = 1) (hb : d370410 q = 1) : d370455 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d369370, d370410, d370455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369370, d370410, d370455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369371 q = 1) (hb : d370411 q = 1) : d370456 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d369371, d370411, d370456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369371, d370411, d370456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104857 (p : Pattern) (ha : d369377 p = 1) (hb : d370417 p = 1) : d370462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369372 q = 1) (hb : d370412 q = 1) : d370457 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d369372, d370412, d370457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104856 q ha hb
    | true =>
      simp only [d369372, d370412, d370457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369373 q = 1) (hb : d370413 q = 1) : d370458 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d369373, d370413, d370458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369373, d370413, d370458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369374 q = 1) (hb : d370414 q = 1) : d370459 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d369374, d370414, d370459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369374, d370414, d370459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369375 q = 1) (hb : d370415 q = 1) : d370460 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d369375, d370415, d370460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369375, d370415, d370460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369376 q = 1) (hb : d370416 q = 1) : d370461 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d369376, d370416, d370461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369376, d370416, d370461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369377 q = 1) (hb : d370417 q = 1) : d370462 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d369377, d370417, d370462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369377, d370417, d370462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104858 (p : Pattern) (ha : d369383 p = 1) (hb : d370423 p = 1) : d370468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369378 q = 1) (hb : d370418 q = 1) : d370463 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d369378, d370418, d370463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104857 q ha hb
    | true =>
      simp only [d369378, d370418, d370463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369379 q = 1) (hb : d370419 q = 1) : d370464 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d369379, d370419, d370464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369379, d370419, d370464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369380 q = 1) (hb : d370420 q = 1) : d370465 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d369380, d370420, d370465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369380, d370420, d370465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369381 q = 1) (hb : d370421 q = 1) : d370466 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d369381, d370421, d370466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369381, d370421, d370466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369382 q = 1) (hb : d370422 q = 1) : d370467 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d369382, d370422, d370467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369382, d370422, d370467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369383 q = 1) (hb : d370423 q = 1) : d370468 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d369383, d370423, d370468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369383, d370423, d370468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104859 (p : Pattern) (ha : d271212 p = 1) (hb : d321880 p = 1) : d370554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46532 q = 1) (hb : d271212 q = 1) : d370164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104486 q ha hb
    | true =>
      simp only [d46532, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104487 q ha hb
  have h2 (q : Pattern) (ha : d46533 q = 1) (hb : d271212 q = 1) : d370165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46533, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46534 q = 1) (hb : d271212 q = 1) : d370166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46534, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46535 q = 1) (hb : d271212 q = 1) : d370167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46536 q = 1) (hb : d271212 q = 1) : d370168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d321880 q = 1) : d370554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321880, d370554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321880, d370554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104860 (p : Pattern) (ha : d271212 p = 1) (hb : d321891 p = 1) : d370565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d321886 q = 1) : d370560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d321886, d370560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104523 q hb ha
    | true =>
      simp only [d321886, d370560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104495 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d321887 q = 1) : d370561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321887, d370561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321887, d370561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d321888 q = 1) : d370562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321888, d370562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321888, d370562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d321889 q = 1) : d370563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321889, d370563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321889, d370563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d321890 q = 1) : d370564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321890, d370564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321890, d370564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d321891 q = 1) : d370565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321891, d370565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321891, d370565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104861 (p : Pattern) (ha : d271212 p = 1) (hb : d321897 p = 1) : d370571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d271212 q = 1) : d370170 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d370170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104485 q ha hb
    | true =>
      simp only [d46538, d370170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104488 q ha hb
  have h2 (q : Pattern) (ha : d46539 q = 1) (hb : d271212 q = 1) : d370171 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d370171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, d370171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d321878 q = 1) : d370552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321878, d370552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d321878, d370552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d321879 q = 1) : d370553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321879, d370553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321879, d370553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d321881 q = 1) : d370555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321881, d370555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321881, d370555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104859 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d321882 q = 1) : d370556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321882, d370556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321882, d370556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d321883 q = 1) : d370557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321883, d370557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321883, d370557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d321884 q = 1) : d370558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321884, d370558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321884, d370558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d321885 q = 1) : d370559 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321885, d370559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321885, d370559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d321892 q = 1) : d370566 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321892, d370566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321892, d370566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104860 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d321893 q = 1) : d370567 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321893, d370567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321893, d370567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d321894 q = 1) : d370568 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321894, d370568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d321894, d370568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d321895 q = 1) : d370569 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321895, d370569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321895, d370569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d321896 q = 1) : d370570 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321896, d370570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321896, d370570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d321897 q = 1) : d370571 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321897, d370571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321897, d370571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104862 (p : Pattern) (ha : d271212 p = 1) (hb : d321903 p = 1) : d370577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d321898 q = 1) : d370572 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321898, d370572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321898, d370572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104861 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d321899 q = 1) : d370573 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321899, d370573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321899, d370573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d321900 q = 1) : d370574 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321900, d370574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321900, d370574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d321901 q = 1) : d370575 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321901, d370575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321901, d370575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d321902 q = 1) : d370576 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321902, d370576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321902, d370576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d321903 q = 1) : d370577 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321903, d370577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321903, d370577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104863 (p : Pattern) (ha : d271212 p = 1) (hb : d321910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46926 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104541 q ha hb
    | true =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104542 q ha hb
  have h2 (q : Pattern) (ha : d46927 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46928 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46929 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46930 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d321910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104864 (p : Pattern) (ha : d271212 p = 1) (hb : d326581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d326576 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d326577 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d271212, d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d271212, d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d326578 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d46871 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46872 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46872, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d46873 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d326579 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d326580 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d326581 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h10 p ha hb
theorem andIntro104865 (p : Pattern) (ha : d271212 p = 1) (hb : d326587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104531 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104531 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47095 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47101 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104534 q ha hb
  have h9 (q : Pattern) (ha : d46889 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104534 q ha hb
    | true =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d47102 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d326582 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104864 q ha hb
    | true =>
      simp only [d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d326583 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d326584 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d326585 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d326586 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d271212 q = 1) (hb : d326587 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104866 (p : Pattern) (ha : d271212 p = 1) (hb : d326593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d326588 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104547 q hb ha
    | true =>
      simp only [d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104865 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d326589 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d326590 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d326591 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d326592 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d326593 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104867 (p : Pattern) (ha : d271212 p = 1) (hb : d326599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d326594 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104866 q ha hb
    | true =>
      simp only [d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d326595 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d326596 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d326597 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d326598 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d326599 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104868 (p : Pattern) (ha : d271212 p = 1) (hb : d326605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d326600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104574 q hb ha
    | true =>
      simp only [d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104867 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d326601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d326602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d326603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d326604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d326605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104869 (p : Pattern) (ha : d271212 p = 1) (hb : d326611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104540 q ha hb
    | true =>
      simp only [d46932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104543 q ha hb
  have h2 (q : Pattern) (ha : d46933 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104863 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d326606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104868 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d326607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d326608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d326609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d326610 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d326611 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104870 (p : Pattern) (ha : d271212 p = 1) (hb : d326617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d326612 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104869 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d326613 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d326614 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d326615 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d326616 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d326617 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104871 (p : Pattern) (ha : d271212 p = 1) (hb : d367603 p = 1) : d275820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44916 q = 1) (hb : d271212 q = 1) : d275530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d275530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104587 q ha hb
    | true =>
      simp only [d44916, d275530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68740 q ha hb
  have h2 (q : Pattern) (ha : d44976 q = 1) (hb : d271212 q = 1) : d275588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d275588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44976, d275588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44977 q = 1) (hb : d271212 q = 1) : d275589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d275589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44977, d275589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44978 q = 1) (hb : d271212 q = 1) : d275590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d275590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44978, d275590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44979 q = 1) (hb : d271212 q = 1) : d275591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d275591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44979, d275591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367603 q = 1) : d275820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367603, d275820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367603, d275820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104872 (p : Pattern) (ha : d271212 p = 1) (hb : d367613 p = 1) : d275870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44952 q = 1) (hb : d271212 q = 1) : d275564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44952, d275564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104592 q ha hb
    | true =>
      simp only [d44952, d275564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68745 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367609 q = 1) : d275866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367609, d275866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367609, d275866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367610 q = 1) : d275867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367610, d275867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367610, d275867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367611 q = 1) : d275868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367611, d275868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367611, d275868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367612 q = 1) : d275869 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367612, d275869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367612, d275869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367613 q = 1) : d275870 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367613, d275870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367613, d275870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104873 (p : Pattern) (ha : d271212 p = 1) (hb : d367619 p = 1) : d277233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44981 q = 1) (hb : d271212 q = 1) : d275593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d275593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104595 q ha hb
    | true =>
      simp only [d44981, d275593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104596 q ha hb
  have h2 (q : Pattern) (ha : d44982 q = 1) (hb : d271212 q = 1) : d275594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d275594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44982, d275594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367601 q = 1) : d277223 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367601, d277223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367601, d277223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367602 q = 1) : d277224 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367602, d277224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367602, d277224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367604 q = 1) : d275821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367604, d275821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367604, d275821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104871 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367605 q = 1) : d277225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367605, d277225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367605, d277225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d367606 q = 1) : d277226 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367606, d277226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367606, d277226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d367607 q = 1) : d277227 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367607, d277227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367607, d277227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d367608 q = 1) : d277228 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367608, d277228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367608, d277228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d367614 q = 1) : d275871 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367614, d275871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367614, d275871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104872 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d367615 q = 1) : d277229 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367615, d277229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367615, d277229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d367616 q = 1) : d277230 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367616, d277230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367616, d277230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d367617 q = 1) : d277231 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367617, d277231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367617, d277231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d367618 q = 1) : d277232 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367618, d277232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367618, d277232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d367619 q = 1) : d277233 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367619, d277233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367619, d277233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104874 (p : Pattern) (ha : d271212 p = 1) (hb : d367625 p = 1) : d277239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69458 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367620 q = 1) : d277234 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367620, d277234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367620, d277234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104873 q ha hb
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d367621 q = 1) : d277235 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367621, d277235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367621, d277235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d367622 q = 1) : d277236 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367622, d277236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367622, d277236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d367623 q = 1) : d277237 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367623, d277237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367623, d277237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d367624 q = 1) : d277238 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367624, d277238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367624, d277238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d367625 q = 1) : d277239 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367625, d277239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d367625, d277239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104875 (p : Pattern) (ha : d271212 p = 1) (hb : d367628 p = 1) : d370471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45200 q = 1) (hb : d271212 q = 1) : d369416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d369416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104626 q ha hb
    | true =>
      simp only [d45200, d369416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104627 q ha hb
  have h2 (q : Pattern) (ha : d45201 q = 1) (hb : d271212 q = 1) : d369477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d369477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45201, d369477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45202 q = 1) (hb : d271212 q = 1) : d369478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d369478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45202, d369478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45203 q = 1) (hb : d271212 q = 1) : d369479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d369479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45203, d369479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45204 q = 1) (hb : d271212 q = 1) : d369480 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d369480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45204, d369480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367628 q = 1) : d370471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367628, d370471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367628, d370471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104876 (p : Pattern) (ha : d271212 p = 1) (hb : d367639 p = 1) : d370481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367634 q = 1) : d369452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367634, d369452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104663 q hb ha
    | true =>
      simp only [d367634, d369452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104633 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367635 q = 1) : d370477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367635, d370477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367635, d370477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367636 q = 1) : d370478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367636, d370478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367636, d370478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367637 q = 1) : d370479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367637, d370479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367637, d370479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367638 q = 1) : d370480 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367638, d370480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367638, d370480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367639 q = 1) : d370481 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367639, d370481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367639, d370481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104877 (p : Pattern) (ha : d271212 p = 1) (hb : d367645 p = 1) : d370487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45206 q = 1) (hb : d271212 q = 1) : d369482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45206, d369482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104625 q ha hb
    | true =>
      simp only [d45206, d369482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104628 q ha hb
  have h2 (q : Pattern) (ha : d45207 q = 1) (hb : d271212 q = 1) : d369483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45207, d369483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45207, d369483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367626 q = 1) : d370469 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367626, d370469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367626, d370469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367627 q = 1) : d370470 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367627, d370470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367627, d370470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367629 q = 1) : d370472 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367629, d370472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367629, d370472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104875 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367630 q = 1) : d370473 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367630, d370473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367630, d370473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d367631 q = 1) : d370474 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367631, d370474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367631, d370474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d367632 q = 1) : d370475 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367632, d370475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367632, d370475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d367633 q = 1) : d370476 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367633, d370476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367633, d370476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d367640 q = 1) : d370482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367640, d370482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367640, d370482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104876 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d367641 q = 1) : d370483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367641, d370483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367641, d370483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d367642 q = 1) : d370484 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367642, d370484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367642, d370484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d367643 q = 1) : d370485 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367643, d370485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367643, d370485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d367644 q = 1) : d370486 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367644, d370486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367644, d370486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d367645 q = 1) : d370487 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367645, d370487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367645, d370487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104878 (p : Pattern) (ha : d271212 p = 1) (hb : d367651 p = 1) : d370493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367646 q = 1) : d370488 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367646, d370488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367646, d370488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104877 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367647 q = 1) : d370489 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367647, d370489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367647, d370489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367648 q = 1) : d370490 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367648, d370490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367648, d370490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367649 q = 1) : d370491 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367649, d370491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367649, d370491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367650 q = 1) : d370492 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367650, d370492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367650, d370492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367651 q = 1) : d370493 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367651, d370493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367651, d370493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104879 (p : Pattern) (ha : d271212 p = 1) (hb : d367655 p = 1) : d370497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45542 q = 1) (hb : d271212 q = 1) : d369650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45542, d369650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104677 q ha hb
    | true =>
      simp only [d45542, d369650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104678 q ha hb
  have h2 (q : Pattern) (ha : d45543 q = 1) (hb : d271212 q = 1) : d369651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d369651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45543, d369651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45544 q = 1) (hb : d271212 q = 1) : d369652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d369652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45544, d369652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45545 q = 1) (hb : d271212 q = 1) : d369653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d369653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45545, d369653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45546 q = 1) (hb : d271212 q = 1) : d369654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d369654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45546, d369654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367655 q = 1) : d370497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367655, d370497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367655, d370497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104880 (p : Pattern) (ha : d271212 p = 1) (hb : d367666 p = 1) : d370508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367661 q = 1) : d370503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367661, d370503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104718 q hb ha
    | true =>
      simp only [d367661, d370503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104686 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367662 q = 1) : d370504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367662, d370504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367662, d370504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367663 q = 1) : d370505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367663, d370505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367663, d370505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367664 q = 1) : d370506 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367664, d370506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367664, d370506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367665 q = 1) : d370507 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367665, d370507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367665, d370507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367666 q = 1) : d370508 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367666, d370508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367666, d370508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104881 (p : Pattern) (ha : d271212 p = 1) (hb : d367672 p = 1) : d370514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45548 q = 1) (hb : d271212 q = 1) : d369656 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45548, d369656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104676 q ha hb
    | true =>
      simp only [d45548, d369656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104679 q ha hb
  have h2 (q : Pattern) (ha : d45549 q = 1) (hb : d271212 q = 1) : d369657 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45549, d369657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45549, d369657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367653 q = 1) : d370495 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367653, d370495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367653, d370495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367654 q = 1) : d370496 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367654, d370496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367654, d370496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367656 q = 1) : d370498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367656, d370498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367656, d370498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104879 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367657 q = 1) : d370499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367657, d370499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367657, d370499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d367658 q = 1) : d370500 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367658, d370500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367658, d370500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d367659 q = 1) : d370501 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367659, d370501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367659, d370501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d367660 q = 1) : d370502 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367660, d370502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367660, d370502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d367667 q = 1) : d370509 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367667, d370509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367667, d370509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104880 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d367668 q = 1) : d370510 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367668, d370510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367668, d370510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d367669 q = 1) : d370511 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367669, d370511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367669, d370511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d367670 q = 1) : d370512 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367670, d370512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367670, d370512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d367671 q = 1) : d370513 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367671, d370513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367671, d370513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d367672 q = 1) : d370514 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367672, d370514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367672, d370514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104882 (p : Pattern) (ha : d271212 p = 1) (hb : d367678 p = 1) : d370520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367673 q = 1) : d370515 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367673, d370515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367673, d370515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104881 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367674 q = 1) : d370516 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367674, d370516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367674, d370516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367675 q = 1) : d370517 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367675, d370517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367675, d370517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367676 q = 1) : d370518 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367676, d370518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367676, d370518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367677 q = 1) : d370519 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367677, d370519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367677, d370519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367678 q = 1) : d370520 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367678, d370520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367678, d370520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104883 (p : Pattern) (ha : d271212 p = 1) (hb : d367683 p = 1) : d370525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46006 q = 1) (hb : d271212 q = 1) : d369900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46006, d369900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104737 q ha hb
    | true =>
      simp only [d46006, d369900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104738 q ha hb
  have h2 (q : Pattern) (ha : d46007 q = 1) (hb : d271212 q = 1) : d369901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d369901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46007, d369901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46008 q = 1) (hb : d271212 q = 1) : d369902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d369902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46008, d369902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46009 q = 1) (hb : d271212 q = 1) : d369903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d369903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46009, d369903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46010 q = 1) (hb : d271212 q = 1) : d369904 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d369904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46010, d369904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367683 q = 1) : d370525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367683, d370525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367683, d370525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro104884 (p : Pattern) (ha : d271212 p = 1) (hb : d367694 p = 1) : d370536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367689 q = 1) : d370531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367689, d370531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104778 q hb ha
    | true =>
      simp only [d367689, d370531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104746 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367690 q = 1) : d370532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367690, d370532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367690, d370532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367691 q = 1) : d370533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367691, d370533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367691, d370533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367692 q = 1) : d370534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367692, d370534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367692, d370534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367693 q = 1) : d370535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367693, d370535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367693, d370535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367694 q = 1) : d370536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367694, d370536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367694, d370536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104885 (p : Pattern) (ha : d271212 p = 1) (hb : d367700 p = 1) : d370542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46012 q = 1) (hb : d271212 q = 1) : d369906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d369906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104736 q ha hb
    | true =>
      simp only [d46012, d369906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104739 q ha hb
  have h2 (q : Pattern) (ha : d46013 q = 1) (hb : d271212 q = 1) : d369907 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d369907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46013, d369907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367681 q = 1) : d370523 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367681, d370523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367681, d370523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367682 q = 1) : d370524 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367682, d370524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367682, d370524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367684 q = 1) : d370526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367684, d370526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367684, d370526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104883 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367685 q = 1) : d370527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367685, d370527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367685, d370527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d367686 q = 1) : d370528 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367686, d370528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367686, d370528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d367687 q = 1) : d370529 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367687, d370529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367687, d370529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d367688 q = 1) : d370530 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367688, d370530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367688, d370530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d367695 q = 1) : d370537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367695, d370537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367695, d370537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104884 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d367696 q = 1) : d370538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367696, d370538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367696, d370538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d367697 q = 1) : d370539 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367697, d370539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367697, d370539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d367698 q = 1) : d370540 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367698, d370540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367698, d370540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d367699 q = 1) : d370541 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367699, d370541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367699, d370541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d367700 q = 1) : d370542 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367700, d370542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367700, d370542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104886 (p : Pattern) (ha : d271212 p = 1) (hb : d367706 p = 1) : d370548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367701 q = 1) : d370543 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367701, d370543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367701, d370543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104885 q ha hb
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367702 q = 1) : d370544 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367702, d370544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367702, d370544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367703 q = 1) : d370545 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367703, d370545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367703, d370545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367704 q = 1) : d370546 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367704, d370546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367704, d370546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367705 q = 1) : d370547 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367705, d370547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367705, d370547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367706 q = 1) : d370548 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367706, d370548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367706, d370548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104887 (p : Pattern) (ha : d271212 p = 1) (hb : d367712 p = 1) : d370583 p = 1 := by
  have h0 (q : Pattern) (ha : d271212 q = 1) (hb : d367652 q = 1) : d370494 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367652, d370494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104874 q ha hb
    | true =>
      simp only [d367652, d370494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104878 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367679 q = 1) : d370521 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367679, d370521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367679, d370521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104882 q ha hb
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367680 q = 1) : d370522 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367680, d370522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d367680, d370522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367707 q = 1) : d370549 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367707, d370549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367707, d370549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104886 q ha hb
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367708 q = 1) : d370550 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367708, d370550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367708, d370550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367709 q = 1) : d370551 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d367709, d370551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367709, d370551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271212 q = 1) (hb : d321904 q = 1) : d370578 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321904, d370578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321904, d370578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104862 q ha hb
  have h8 (q : Pattern) (ha : d271212 q = 1) (hb : d321905 q = 1) : d370579 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321905, d370579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321905, d370579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271212 q = 1) (hb : d321906 q = 1) : d370580 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321906, d370580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321906, d370580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271212 q = 1) (hb : d367710 q = 1) : d370581 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d367710, d370581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367710, d370581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271212 q = 1) (hb : d326618 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104870 q ha hb
  have h12 (q : Pattern) (ha : d271212 q = 1) (hb : d326619 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271212 q = 1) (hb : d326620 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271212 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271212 q = 1) (hb : d367711 q = 1) : d370582 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d367711, d370582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367711, d370582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d271212 q = 1) (hb : d367712 q = 1) : d370583 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d367712, d370583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d367712, d370583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro104888 (p : Pattern) (ha : d271212 p = 1) (hb : d367718 p = 1) : d370589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367713 q = 1) : d370584 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d367713, d370584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104887 q ha hb
    | true =>
      simp only [d367713, d370584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367714 q = 1) : d370585 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d367714, d370585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367714, d370585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367715 q = 1) : d370586 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d367715, d370586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367715, d370586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367716 q = 1) : d370587 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d367716, d370587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367716, d370587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367717 q = 1) : d370588 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d367717, d370588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367717, d370588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367718 q = 1) : d370589 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d367718, d370589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367718, d370589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104889 (p : Pattern) (ha : d271212 p = 1) (hb : d367724 p = 1) : d370595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367719 q = 1) : d370590 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d367719, d370590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104888 q ha hb
    | true =>
      simp only [d367719, d370590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367720 q = 1) : d370591 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d367720, d370591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367720, d370591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367721 q = 1) : d370592 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d367721, d370592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367721, d370592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367722 q = 1) : d370593 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, d370593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367722, d370593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367723 q = 1) : d370594 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d370594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367723, d370594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367724 q = 1) : d370595 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, d370595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367724, d370595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104890 (p : Pattern) (ha : d271212 p = 1) (hb : d367730 p = 1) : d370601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367725 q = 1) : d370596 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, d370596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104889 q ha hb
    | true =>
      simp only [d367725, d370596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367726 q = 1) : d370597 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, d370597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, d370597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367727 q = 1) : d370598 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, d370598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, d370598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367728 q = 1) : d370599 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, d370599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, d370599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367729 q = 1) : d370600 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, d370600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, d370600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367730 q = 1) : d370601 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, d370601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, d370601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104891 (p : Pattern) (ha : d271212 p = 1) (hb : d367736 p = 1) : d370607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367731 q = 1) : d370602 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, d370602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104890 q ha hb
    | true =>
      simp only [d367731, d370602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367732 q = 1) : d370603 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, d370603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, d370603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367733 q = 1) : d370604 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, d370604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, d370604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367734 q = 1) : d370605 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, d370605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, d370605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367735 q = 1) : d370606 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, d370606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, d370606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367736 q = 1) : d370607 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, d370607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, d370607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104892 (p : Pattern) (ha : d271212 p = 1) (hb : d367742 p = 1) : d370613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367737 q = 1) : d370608 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, d370608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104891 q ha hb
    | true =>
      simp only [d367737, d370608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367738 q = 1) : d370609 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, d370609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, d370609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367739 q = 1) : d370610 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, d370610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, d370610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367740 q = 1) : d370611 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, d370611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, d370611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367741 q = 1) : d370612 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, d370612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, d370612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367742 q = 1) : d370613 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, d370613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, d370613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104893 (p : Pattern) (ha : d271212 p = 1) (hb : d367748 p = 1) : d370619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367743 q = 1) : d370614 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, d370614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104892 q ha hb
    | true =>
      simp only [d367743, d370614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367744 q = 1) : d370615 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, d370615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, d370615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367745 q = 1) : d370616 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, d370616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, d370616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367746 q = 1) : d370617 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, d370617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, d370617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367747 q = 1) : d370618 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, d370618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, d370618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367748 q = 1) : d370619 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, d370619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, d370619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104894 (p : Pattern) (ha : d271212 p = 1) (hb : d367754 p = 1) : d370625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271212 q = 1) (hb : d367749 q = 1) : d370620 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, d370620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104893 q ha hb
    | true =>
      simp only [d367749, d370620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d271212 q = 1) (hb : d367750 q = 1) : d370621 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, d370621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, d370621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d271212 q = 1) (hb : d367751 q = 1) : d370622 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, d370622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, d370622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d271212 q = 1) (hb : d367752 q = 1) : d370623 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, d370623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, d370623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d271212 q = 1) (hb : d367753 q = 1) : d370624 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, d370624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, d370624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d271212 q = 1) (hb : d367754 q = 1) : d370625 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, d370625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, d370625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104895 (p : Pattern) (ha : d368891 p = 1) (hb : d370159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d368841 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d368864 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d368815 q = 1) (hb : d370154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104803 q ha hb
    | true =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104804 q ha hb
  have h5 (q : Pattern) (ha : d368865 q = 1) (hb : d370155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368865, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d368865, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d368887 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d368888 q = 1) (hb : d370156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368888, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d368888, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d368889 q = 1) (hb : d370157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368889, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d368889, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d368890 q = 1) (hb : d370158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368890, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d368890, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d368891 q = 1) (hb : d370159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368891, d370159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368891, d370159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104896 (p : Pattern) (ha : d368912 p = 1) (hb : d370169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d368841 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d368850 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368864 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d368815 q = 1) (hb : d370154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104803 q ha hb
    | true =>
      simp only [d368815, d370154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104804 q ha hb
  have h4 (q : Pattern) (ha : d368865 q = 1) (hb : d370155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368865, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d368865, d370155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d368887 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d368888 q = 1) (hb : d370156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368888, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d368888, d370156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d368889 q = 1) (hb : d370157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368889, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d368889, d370157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368890 q = 1) (hb : d370158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368890, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368890, d370158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d368897 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d368902 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d368904 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d368825 q = 1) (hb : d370164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368825, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104806 q ha hb
    | true =>
      simp only [d368825, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104807 q ha hb
  have h13 (q : Pattern) (ha : d368905 q = 1) (hb : d370165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368905, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d368905, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d368908 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d368909 q = 1) (hb : d370166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368909, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d368909, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d368910 q = 1) (hb : d370167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368910, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d368910, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d368911 q = 1) (hb : d370168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368911, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d368911, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d368912 q = 1) (hb : d370169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368912, d370169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d368912, d370169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104897 (p : Pattern) (ha : d368932 p = 1) (hb : d370554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d368904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d368825 q = 1) (hb : d370164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368825, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104806 q ha hb
    | true =>
      simp only [d368825, d370164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104807 q ha hb
  have h3 (q : Pattern) (ha : d368905 q = 1) (hb : d370165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368905, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d368905, d370165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d368908 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d368909 q = 1) (hb : d370166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d368909, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368909, d370166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d368930 q = 1) (hb : d370167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d368930, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368930, d370167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368931 q = 1) (hb : d370168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d368931, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368931, d370168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d368932 q = 1) (hb : d370554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d368932, d370554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368932, d370554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104898 (p : Pattern) (ha : d369018 p = 1) (hb : d370565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d368987 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d368992 q = 1) (hb : d370560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368992, d370560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104841 q ha hb
    | true =>
      simp only [d368992, d370560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104847 q ha hb
  have h3 (q : Pattern) (ha : d368993 q = 1) (hb : d370561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d368993, d370561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d368993, d370561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d369014 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d369015 q = 1) (hb : d370562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d369015, d370562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369015, d370562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d369016 q = 1) (hb : d370563 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d369016, d370563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369016, d370563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d369017 q = 1) (hb : d370564 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d369017, d370564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369017, d370564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d369018 q = 1) (hb : d370565 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d369018, d370565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369018, d370565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104899 (p : Pattern) (ha : d369031 p = 1) (hb : d370571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d368833 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d368913 q = 1) (hb : d370170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368913, d370170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104895 q ha hb
    | true =>
      simp only [d368913, d370170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104896 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d368927 q = 1) (hb : d370171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368927, d370171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d368927, d370171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d368928 q = 1) (hb : d370552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368928, d370552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d368928, d370552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d368929 q = 1) (hb : d370553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368929, d370553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d368929, d370553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d368933 q = 1) (hb : d370555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d368933, d370555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d368933, d370555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104897 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d368935 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d368936 q = 1) (hb : d370556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d368936, d370556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d368936, d370556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d368937 q = 1) (hb : d370557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d368937, d370557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d368937, d370557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d368938 q = 1) (hb : d370558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d368938, d370558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d368938, d370558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d368939 q = 1) (hb : d370559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d368939, d370559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d368939, d370559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d369019 q = 1) (hb : d370566 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d369019, d370566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d369019, d370566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104898 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d369026 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d369027 q = 1) (hb : d370567 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d369027, d370567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d369027, d370567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d369028 q = 1) (hb : d370568 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d369028, d370568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d369028, d370568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d369029 q = 1) (hb : d370569 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d369029, d370569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d369029, d370569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d369030 q = 1) (hb : d370570 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d369030, d370570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d369030, d370570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d369031 q = 1) (hb : d370571 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d369031, d370571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d369031, d370571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104900 (p : Pattern) (ha : d369037 p = 1) (hb : d370577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369032 q = 1) (hb : d370572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d369032, d370572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369032, d370572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104899 q ha hb
  have h2 (q : Pattern) (ha : d369033 q = 1) (hb : d370573 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d369033, d370573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369033, d370573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d369034 q = 1) (hb : d370574 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d369034, d370574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369034, d370574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d369035 q = 1) (hb : d370575 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d369035, d370575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369035, d370575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d369036 q = 1) (hb : d370576 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d369036, d370576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369036, d370576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d369037 q = 1) (hb : d370577 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d369037, d370577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d369037, d370577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104901 (p : Pattern) (ha : d369341 p = 1) (hb : d370583 p = 1) : d370628 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d370551 q = 1) : d370551 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d369038 q = 1) (hb : d370578 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d369038, d370578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d369038, d370578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104900 q ha hb
  have h3 (q : Pattern) (ha : d369039 q = 1) (hb : d370579 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d369039, d370579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d369039, d370579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d369040 q = 1) (hb : d370580 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d369040, d370580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d369040, d370580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d369041 q = 1) (hb : d370581 q = 1) : d370626 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d369041, d370581, d370626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d369041, d370581, d370626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d369339 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d369340 q = 1) (hb : d370582 q = 1) : d370627 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d369340, d370582, d370627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369340, d370582, d370627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d369341 q = 1) (hb : d370583 q = 1) : d370628 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d369341, d370583, d370628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d369341, d370583, d370628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro104902 (p : Pattern) (ha : d369347 p = 1) (hb : d370589 p = 1) : d370634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369342 q = 1) (hb : d370584 q = 1) : d370629 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d369342, d370584, d370629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104901 q ha hb
    | true =>
      simp only [d369342, d370584, d370629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369343 q = 1) (hb : d370585 q = 1) : d370630 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d369343, d370585, d370630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369343, d370585, d370630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369344 q = 1) (hb : d370586 q = 1) : d370631 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d369344, d370586, d370631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369344, d370586, d370631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369345 q = 1) (hb : d370587 q = 1) : d370632 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d369345, d370587, d370632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369345, d370587, d370632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369346 q = 1) (hb : d370588 q = 1) : d370633 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d369346, d370588, d370633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369346, d370588, d370633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369347 q = 1) (hb : d370589 q = 1) : d370634 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d369347, d370589, d370634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369347, d370589, d370634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104903 (p : Pattern) (ha : d369353 p = 1) (hb : d370595 p = 1) : d370640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369348 q = 1) (hb : d370590 q = 1) : d370635 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d369348, d370590, d370635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104902 q ha hb
    | true =>
      simp only [d369348, d370590, d370635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369349 q = 1) (hb : d370591 q = 1) : d370636 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d369349, d370591, d370636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369349, d370591, d370636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369350 q = 1) (hb : d370592 q = 1) : d370637 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d369350, d370592, d370637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369350, d370592, d370637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369351 q = 1) (hb : d370593 q = 1) : d370638 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d369351, d370593, d370638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369351, d370593, d370638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369352 q = 1) (hb : d370594 q = 1) : d370639 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d369352, d370594, d370639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369352, d370594, d370639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369353 q = 1) (hb : d370595 q = 1) : d370640 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d369353, d370595, d370640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369353, d370595, d370640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104904 (p : Pattern) (ha : d369359 p = 1) (hb : d370601 p = 1) : d370646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369354 q = 1) (hb : d370596 q = 1) : d370641 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d369354, d370596, d370641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104903 q ha hb
    | true =>
      simp only [d369354, d370596, d370641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369355 q = 1) (hb : d370597 q = 1) : d370642 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d369355, d370597, d370642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369355, d370597, d370642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369356 q = 1) (hb : d370598 q = 1) : d370643 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d369356, d370598, d370643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369356, d370598, d370643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369357 q = 1) (hb : d370599 q = 1) : d370644 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d369357, d370599, d370644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369357, d370599, d370644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369358 q = 1) (hb : d370600 q = 1) : d370645 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d369358, d370600, d370645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369358, d370600, d370645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369359 q = 1) (hb : d370601 q = 1) : d370646 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d369359, d370601, d370646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369359, d370601, d370646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104905 (p : Pattern) (ha : d369365 p = 1) (hb : d370607 p = 1) : d370652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369360 q = 1) (hb : d370602 q = 1) : d370647 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d369360, d370602, d370647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104904 q ha hb
    | true =>
      simp only [d369360, d370602, d370647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369361 q = 1) (hb : d370603 q = 1) : d370648 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d369361, d370603, d370648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369361, d370603, d370648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369362 q = 1) (hb : d370604 q = 1) : d370649 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d369362, d370604, d370649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369362, d370604, d370649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369363 q = 1) (hb : d370605 q = 1) : d370650 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d369363, d370605, d370650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369363, d370605, d370650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369364 q = 1) (hb : d370606 q = 1) : d370651 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d369364, d370606, d370651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369364, d370606, d370651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369365 q = 1) (hb : d370607 q = 1) : d370652 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d369365, d370607, d370652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369365, d370607, d370652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104906 (p : Pattern) (ha : d369371 p = 1) (hb : d370613 p = 1) : d370658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369366 q = 1) (hb : d370608 q = 1) : d370653 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d369366, d370608, d370653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104905 q ha hb
    | true =>
      simp only [d369366, d370608, d370653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369367 q = 1) (hb : d370609 q = 1) : d370654 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d369367, d370609, d370654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369367, d370609, d370654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369368 q = 1) (hb : d370610 q = 1) : d370655 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d369368, d370610, d370655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369368, d370610, d370655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369369 q = 1) (hb : d370611 q = 1) : d370656 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d369369, d370611, d370656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369369, d370611, d370656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369370 q = 1) (hb : d370612 q = 1) : d370657 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d369370, d370612, d370657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369370, d370612, d370657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369371 q = 1) (hb : d370613 q = 1) : d370658 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d369371, d370613, d370658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369371, d370613, d370658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104907 (p : Pattern) (ha : d369377 p = 1) (hb : d370619 p = 1) : d370664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369372 q = 1) (hb : d370614 q = 1) : d370659 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d369372, d370614, d370659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104906 q ha hb
    | true =>
      simp only [d369372, d370614, d370659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369373 q = 1) (hb : d370615 q = 1) : d370660 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d369373, d370615, d370660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369373, d370615, d370660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369374 q = 1) (hb : d370616 q = 1) : d370661 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d369374, d370616, d370661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369374, d370616, d370661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369375 q = 1) (hb : d370617 q = 1) : d370662 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d369375, d370617, d370662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369375, d370617, d370662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369376 q = 1) (hb : d370618 q = 1) : d370663 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d369376, d370618, d370663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369376, d370618, d370663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369377 q = 1) (hb : d370619 q = 1) : d370664 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d369377, d370619, d370664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369377, d370619, d370664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104908 (p : Pattern) (ha : d369383 p = 1) (hb : d370625 p = 1) : d370670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d369378 q = 1) (hb : d370620 q = 1) : d370665 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d369378, d370620, d370665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104907 q ha hb
    | true =>
      simp only [d369378, d370620, d370665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d369379 q = 1) (hb : d370621 q = 1) : d370666 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d369379, d370621, d370666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d369379, d370621, d370666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d369380 q = 1) (hb : d370622 q = 1) : d370667 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d369380, d370622, d370667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d369380, d370622, d370667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d369381 q = 1) (hb : d370623 q = 1) : d370668 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d369381, d370623, d370668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d369381, d370623, d370668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d369382 q = 1) (hb : d370624 q = 1) : d370669 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d369382, d370624, d370669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d369382, d370624, d370669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d369383 q = 1) (hb : d370625 q = 1) : d370670 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d369383, d370625, d370670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d369383, d370625, d370670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro104909 (p : Pattern) (ha : d370159 p = 1) (hb : d370675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d368057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368066 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d368080 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d370154 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d370155 q = 1) (hb : d370671 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d370155, d370671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370155, d370671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d368149 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d370156 q = 1) (hb : d370672 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d370156, d370672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370156, d370672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d370157 q = 1) (hb : d370673 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d370157, d370673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370157, d370673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d370158 q = 1) (hb : d370674 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d370158, d370674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370158, d370674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d370159 q = 1) (hb : d370675 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d370159, d370675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370159, d370675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104910 (p : Pattern) (ha : d370169 p = 1) (hb : d370680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d368057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d368066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368080 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d370154 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d370155 q = 1) (hb : d370671 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d370155, d370671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370155, d370671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d368149 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d370156 q = 1) (hb : d370672 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d370156, d370672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370156, d370672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d370157 q = 1) (hb : d370673 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d370157, d370673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370157, d370673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d370158 q = 1) (hb : d370674 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d370158, d370674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370158, d370674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d368159 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d368164 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d368166 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d370164 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d370165 q = 1) (hb : d370676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d370165, d370676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d370165, d370676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d368173 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d370166 q = 1) (hb : d370677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d370166, d370677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d370166, d370677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d370167 q = 1) (hb : d370678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d370167, d370678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d370167, d370678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d370168 q = 1) (hb : d370679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d370168, d370679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d370168, d370679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d370169 q = 1) (hb : d370680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d370169, d370680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d370169, d370680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro104911 (p : Pattern) (ha : d370554 p = 1) (hb : d370687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d368166 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d370164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d370165 q = 1) (hb : d370676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d370165, d370676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370165, d370676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d368173 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d370166 q = 1) (hb : d370677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d370166, d370677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370166, d370677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d370167 q = 1) (hb : d370685 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d370167, d370685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370167, d370685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d370168 q = 1) (hb : d370686 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d370168, d370686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370168, d370686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d370554 q = 1) (hb : d370687 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d370554, d370687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370554, d370687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104912 (p : Pattern) (ha : d370565 p = 1) (hb : d370697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d368252 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d370560 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d370561 q = 1) (hb : d370693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d370561, d370693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370561, d370693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d368313 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d370562 q = 1) (hb : d370694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d370562, d370694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370562, d370694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d370563 q = 1) (hb : d370695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d370563, d370695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370563, d370695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d370564 q = 1) (hb : d370696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d370564, d370696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370564, d370696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d370565 q = 1) (hb : d370697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d370565, d370697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370565, d370697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104913 (p : Pattern) (ha : d370571 p = 1) (hb : d370703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d368049 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370170 q = 1) (hb : d370681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d370170, d370681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104909 q ha hb
    | true =>
      simp only [d370170, d370681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104910 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d368191 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d370171 q = 1) (hb : d370682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d370171, d370682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370171, d370682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d370552 q = 1) (hb : d370683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d370552, d370683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370552, d370683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d370553 q = 1) (hb : d370684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d370553, d370684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370553, d370684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d370555 q = 1) (hb : d370688 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d370555, d370688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370555, d370688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104911 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d368200 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d370556 q = 1) (hb : d370689 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d370556, d370689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d370556, d370689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d370557 q = 1) (hb : d370690 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d370557, d370690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d370557, d370690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d370558 q = 1) (hb : d370691 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d370558, d370691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d370558, d370691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d370559 q = 1) (hb : d370692 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d370559, d370692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d370559, d370692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d370566 q = 1) (hb : d370698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d370566, d370698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370566, d370698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104912 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d368329 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d370567 q = 1) (hb : d370699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d370567, d370699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d370567, d370699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d370568 q = 1) (hb : d370700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d370568, d370700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d370568, d370700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d370569 q = 1) (hb : d370701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d370569, d370701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d370569, d370701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d370570 q = 1) (hb : d370702 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d370570, d370702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d370570, d370702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d370571 q = 1) (hb : d370703 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d370571, d370703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d370571, d370703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104914 (p : Pattern) (ha : d370577 p = 1) (hb : d370709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370572 q = 1) (hb : d370704 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d370572, d370704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370572, d370704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104913 q ha hb
  have h2 (q : Pattern) (ha : d370573 q = 1) (hb : d370705 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d370573, d370705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370573, d370705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d370574 q = 1) (hb : d370706 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d370574, d370706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370574, d370706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d370575 q = 1) (hb : d370707 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d370575, d370707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370575, d370707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d370576 q = 1) (hb : d370708 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d370576, d370708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370576, d370708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d370577 q = 1) (hb : d370709 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d370577, d370709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d370577, d370709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104915 (p : Pattern) (ha : d370583 p = 1) (hb : d370758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370551 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370578 q = 1) (hb : d370710 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d370578, d370710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370578, d370710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104914 q ha hb
  have h3 (q : Pattern) (ha : d370579 q = 1) (hb : d370711 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d370579, d370711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370579, d370711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d370580 q = 1) (hb : d370712 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d370580, d370712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370580, d370712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d370581 q = 1) (hb : d370713 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d370581, d370713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d370581, d370713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d370756 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d370582 q = 1) (hb : d370757 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d370582, d370757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370582, d370757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d370583 q = 1) (hb : d370758 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d370583, d370758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d370583, d370758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro104916 (p : Pattern) (ha : d370589 p = 1) (hb : d370764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370584 q = 1) (hb : d370759 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d370584, d370759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104915 q ha hb
    | true =>
      simp only [d370584, d370759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d370585 q = 1) (hb : d370760 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d370585, d370760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370585, d370760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d370586 q = 1) (hb : d370761 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d370586, d370761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370586, d370761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d370587 q = 1) (hb : d370762 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d370587, d370762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370587, d370762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d370588 q = 1) (hb : d370763 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d370588, d370763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370588, d370763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d370589 q = 1) (hb : d370764 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d370589, d370764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370589, d370764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104917 (p : Pattern) (ha : d370595 p = 1) (hb : d370770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370590 q = 1) (hb : d370765 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d370590, d370765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104916 q ha hb
    | true =>
      simp only [d370590, d370765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d370591 q = 1) (hb : d370766 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d370591, d370766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370591, d370766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d370592 q = 1) (hb : d370767 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d370592, d370767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370592, d370767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d370593 q = 1) (hb : d370768 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d370593, d370768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370593, d370768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d370594 q = 1) (hb : d370769 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d370594, d370769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370594, d370769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d370595 q = 1) (hb : d370770 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d370595, d370770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370595, d370770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104918 (p : Pattern) (ha : d370601 p = 1) (hb : d370776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370596 q = 1) (hb : d370771 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d370596, d370771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104917 q ha hb
    | true =>
      simp only [d370596, d370771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d370597 q = 1) (hb : d370772 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d370597, d370772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370597, d370772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d370598 q = 1) (hb : d370773 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d370598, d370773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370598, d370773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d370599 q = 1) (hb : d370774 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d370599, d370774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370599, d370774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d370600 q = 1) (hb : d370775 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d370600, d370775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370600, d370775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d370601 q = 1) (hb : d370776 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d370601, d370776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370601, d370776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104919 (p : Pattern) (ha : d370607 p = 1) (hb : d370782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370602 q = 1) (hb : d370777 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d370602, d370777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104918 q ha hb
    | true =>
      simp only [d370602, d370777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d370603 q = 1) (hb : d370778 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d370603, d370778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370603, d370778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d370604 q = 1) (hb : d370779 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d370604, d370779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370604, d370779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d370605 q = 1) (hb : d370780 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d370605, d370780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370605, d370780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d370606 q = 1) (hb : d370781 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d370606, d370781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370606, d370781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d370607 q = 1) (hb : d370782 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d370607, d370782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370607, d370782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104920 (p : Pattern) (ha : d370613 p = 1) (hb : d370788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370608 q = 1) (hb : d370783 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d370608, d370783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104919 q ha hb
    | true =>
      simp only [d370608, d370783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d370609 q = 1) (hb : d370784 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d370609, d370784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370609, d370784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d370610 q = 1) (hb : d370785 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d370610, d370785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370610, d370785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d370611 q = 1) (hb : d370786 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d370611, d370786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370611, d370786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d370612 q = 1) (hb : d370787 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d370612, d370787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370612, d370787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d370613 q = 1) (hb : d370788 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d370613, d370788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370613, d370788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104921 (p : Pattern) (ha : d370619 p = 1) (hb : d370794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370614 q = 1) (hb : d370789 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d370614, d370789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104920 q ha hb
    | true =>
      simp only [d370614, d370789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d370615 q = 1) (hb : d370790 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d370615, d370790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370615, d370790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d370616 q = 1) (hb : d370791 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d370616, d370791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370616, d370791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d370617 q = 1) (hb : d370792 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d370617, d370792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370617, d370792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d370618 q = 1) (hb : d370793 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d370618, d370793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370618, d370793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d370619 q = 1) (hb : d370794 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d370619, d370794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370619, d370794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104922 (p : Pattern) (ha : d370625 p = 1) (hb : d370800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d370620 q = 1) (hb : d370795 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d370620, d370795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104921 q ha hb
    | true =>
      simp only [d370620, d370795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d370621 q = 1) (hb : d370796 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d370621, d370796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d370621, d370796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d370622 q = 1) (hb : d370797 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d370622, d370797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d370622, d370797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d370623 q = 1) (hb : d370798 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d370623, d370798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d370623, d370798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d370624 q = 1) (hb : d370799 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d370624, d370799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d370624, d370799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d370625 q = 1) (hb : d370800 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d370625, d370800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d370625, d370800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104923 (p : Pattern) (ha : d322250 p = 1) (hb : d370801 p = 1) : d322250 p = 1 := by
  have h0 (q : Pattern) (ha : d322250 q = 1) (hb : d370801 q = 1) : d322250 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro104924 (p : Pattern) (ha : d44884 p = 1) (hb : d318729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44880 q = 1) (hb : d263912 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44881 q = 1) (hb : d318726 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44882 q = 1) (hb : d318727 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44882, d318727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44882, d318727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16 q = 1) (hb : d51868 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44883 q = 1) (hb : d318728 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44883, d318728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44883, d318728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17 q = 1) (hb : d51869 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, d51869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17, d51869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44884 q = 1) (hb : d318729 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44884, d318729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44884, d318729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro104925 (p : Pattern) (ha : d44890 p = 1) (hb : d318735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44888 q = 1) (hb : d318733 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, d318733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44888, d318733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44889 q = 1) (hb : d318734 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, d318734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44889, d318734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d51874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44890 q = 1) (hb : d318735 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44890, d318735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44890, d318735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104926 (p : Pattern) (ha : d44896 p = 1) (hb : d318741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44891 q = 1) (hb : d318736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104925 q ha hb
    | true =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44892 q = 1) (hb : d318737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44893 q = 1) (hb : d318738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44893, d318738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44893, d318738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44894 q = 1) (hb : d318739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44894, d318739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44894, d318739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44895 q = 1) (hb : d318740 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44895, d318740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44895, d318740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44896 q = 1) (hb : d318741 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44896, d318741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44896, d318741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104927 (p : Pattern) (ha : d44902 p = 1) (hb : d318747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44897 q = 1) (hb : d318742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104926 q ha hb
    | true =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d44898 q = 1) (hb : d318743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44899 q = 1) (hb : d318744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d44900 q = 1) (hb : d318745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44900, d318745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44900, d318745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44901 q = 1) (hb : d318746 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44901, d318746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44901, d318746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44902 q = 1) (hb : d318747 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44902, d318747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44902, d318747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro104928 (p : Pattern) (ha : d44908 p = 1) (hb : d318753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d318750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44906 q = 1) (hb : d318751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d318751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44906, d318751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44907 q = 1) (hb : d318752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44907, d318752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44907, d318752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44908 q = 1) (hb : d318753 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44908, d318753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44908, d318753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104929 (p : Pattern) (ha : d318759 p = 1) (hb : d322010 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d44909 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
    | true =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d318755 q = 1) (hb : d322006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318755, d322006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d318755, d322006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d318756 q = 1) (hb : d322007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318756, d322007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318756, d322007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d318757 q = 1) (hb : d322008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318757, d322008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d318757, d322008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d318758 q = 1) (hb : d322009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318758, d322009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318758, d322009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d318759 q = 1) (hb : d322010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318759, d322010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318759, d322010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104930 (p : Pattern) (ha : d44915 p = 1) (hb : d318760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d318750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44906 q = 1) (hb : d318751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d318751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44906, d318751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44907 q = 1) (hb : d318752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44907, d318752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44907, d318752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44915 q = 1) (hb : d318760 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44915, d318760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44915, d318760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104931 (p : Pattern) (ha : d318766 p = 1) (hb : d322015 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d44909 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
    | true =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d318755 q = 1) (hb : d322006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318755, d322006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d318755, d322006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d318756 q = 1) (hb : d322007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318756, d322007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318756, d322007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d318757 q = 1) (hb : d322008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318757, d322008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d318757, d322008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d318758 q = 1) (hb : d322009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318758, d322009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318758, d322009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d44916 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104930 q ha hb
    | true =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d318762 q = 1) (hb : d322011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318762, d322011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d318762, d322011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d318763 q = 1) (hb : d322012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318763, d322012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d318763, d322012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d318764 q = 1) (hb : d322013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318764, d322013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d318764, d322013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d318765 q = 1) (hb : d322014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318765, d322014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d318765, d322014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d318766 q = 1) (hb : d322015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318766, d322015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318766, d322015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro104932 (p : Pattern) (ha : d318773 p = 1) (hb : d322022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44916 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104930 q ha hb
    | true =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318762 q = 1) (hb : d322011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318762, d322011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318762, d322011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d318763 q = 1) (hb : d322012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318763, d322012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318763, d322012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d318771 q = 1) (hb : d322020 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318771, d322020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318771, d322020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318772 q = 1) (hb : d322021 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318772, d322021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318772, d322021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318773 q = 1) (hb : d322022 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318773, d322022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318773, d322022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104933 (p : Pattern) (ha : d44939 p = 1) (hb : d318784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44934 q = 1) (hb : d318779 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44934, d318779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44934, d318779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104925 q ha hb
  have h2 (q : Pattern) (ha : d44891 q = 1) (hb : d318736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104925 q ha hb
    | true =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44935 q = 1) (hb : d318780 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44935, d318780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44935, d318780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44892 q = 1) (hb : d318737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44936 q = 1) (hb : d318781 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44936, d318781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44936, d318781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44937 q = 1) (hb : d318782 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44937, d318782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44937, d318782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44938 q = 1) (hb : d318783 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44938, d318783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44938, d318783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44939 q = 1) (hb : d318784 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44939, d318784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44939, d318784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104934 (p : Pattern) (ha : d44945 p = 1) (hb : d318790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44940 q = 1) (hb : d318785 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104933 q ha hb
    | true =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d44941 q = 1) (hb : d318786 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44942 q = 1) (hb : d318787 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d44943 q = 1) (hb : d318788 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44943, d318788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44943, d318788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44944 q = 1) (hb : d318789 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44944, d318789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44944, d318789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44945 q = 1) (hb : d318790 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44945, d318790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44945, d318790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro104935 (p : Pattern) (ha : d44951 p = 1) (hb : d318796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44946 q = 1) (hb : d318791 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d318791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104934 q ha hb
    | true =>
      simp only [d44946, d318791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44947 q = 1) (hb : d318792 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d318792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d318792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44948 q = 1) (hb : d318793 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44948, d318793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44948, d318793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44949 q = 1) (hb : d318794 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44949, d318794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44949, d318794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44950 q = 1) (hb : d318795 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44950, d318795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44950, d318795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44951 q = 1) (hb : d318796 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44951, d318796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44951, d318796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104936 (p : Pattern) (ha : d318802 p = 1) (hb : d322032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44952 q = 1) (hb : d318797 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44952, d318797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104935 q ha hb
    | true =>
      simp only [d44952, d318797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318798 q = 1) (hb : d322028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318798, d322028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318798, d322028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d318799 q = 1) (hb : d322029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318799, d322029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318799, d322029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d318800 q = 1) (hb : d322030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318800, d322030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318800, d322030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318801 q = 1) (hb : d322031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318801, d322031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318801, d322031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318802 q = 1) (hb : d322032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318802, d322032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318802, d322032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104937 (p : Pattern) (ha : d318808 p = 1) (hb : d322038 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d318767 q = 1) (hb : d322016 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318767, d322016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104929 q ha hb
    | true =>
      simp only [d318767, d322016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104931 q ha hb
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
  have h8 (q : Pattern) (ha : d318768 q = 1) (hb : d322017 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318768, d322017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318768, d322017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d318769 q = 1) (hb : d322018 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318769, d322018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318769, d322018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d318770 q = 1) (hb : d322019 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318770, d322019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d318770, d322019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d318774 q = 1) (hb : d322023 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318774, d322023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318774, d322023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104932 q ha hb
  have h12 (q : Pattern) (ha : d318775 q = 1) (hb : d322024 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318775, d322024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d318775, d322024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d318776 q = 1) (hb : d322025 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318776, d322025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d318776, d322025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d318777 q = 1) (hb : d322026 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318777, d322026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318777, d322026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d318778 q = 1) (hb : d322027 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318778, d322027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318778, d322027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d318803 q = 1) (hb : d322033 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318803, d322033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318803, d322033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104936 q ha hb
  have h17 (q : Pattern) (ha : d318804 q = 1) (hb : d322034 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318804, d322034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d318804, d322034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d318805 q = 1) (hb : d322035 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318805, d322035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d318805, d322035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d318806 q = 1) (hb : d322036 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318806, d322036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d318806, d322036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d318807 q = 1) (hb : d322037 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318807, d322037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d318807, d322037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d318808 q = 1) (hb : d322038 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d318808, d322038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318808, d322038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro104938 (p : Pattern) (ha : d44973 p = 1) (hb : d318818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44909 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
    | true =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d44969 q = 1) (hb : d318814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d318814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d318814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44970 q = 1) (hb : d318815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d318815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44970, d318815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44971 q = 1) (hb : d318816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d318816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d318816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44972 q = 1) (hb : d318817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d318817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d318817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44973 q = 1) (hb : d318818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44973, d318818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44973, d318818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104939 (p : Pattern) (ha : d44980 p = 1) (hb : d318825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44909 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
    | true =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d44969 q = 1) (hb : d318814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d318814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d318814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44970 q = 1) (hb : d318815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d318815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44970, d318815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44971 q = 1) (hb : d318816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d318816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d318816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44972 q = 1) (hb : d318817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d318817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d318817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44916 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104930 q ha hb
    | true =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d44976 q = 1) (hb : d318821 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d318821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44976, d318821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44977 q = 1) (hb : d318822 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d318822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44977, d318822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44978 q = 1) (hb : d318823 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d318823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44978, d318823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44979 q = 1) (hb : d318824 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d318824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44979, d318824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44980 q = 1) (hb : d318825 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44980, d318825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44980, d318825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104940 (p : Pattern) (ha : d45094 p = 1) (hb : d318908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44909 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
    | true =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d44969 q = 1) (hb : d318814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d318814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d318814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44970 q = 1) (hb : d318815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d318815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44970, d318815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44971 q = 1) (hb : d318816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d318816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d318816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44972 q = 1) (hb : d318817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d318817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d318817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d45094 q = 1) (hb : d318908 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45094, d318908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45094, d318908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104941 (p : Pattern) (ha : d44985 p = 1) (hb : d318830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d318750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44906 q = 1) (hb : d318751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d318751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44906, d318751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44984 q = 1) (hb : d318829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44984, d318829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44984, d318829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44985 q = 1) (hb : d318830 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44985, d318830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44985, d318830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104942 (p : Pattern) (ha : d44992 p = 1) (hb : d318837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d318750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44990 q = 1) (hb : d318835 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44990, d318835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44990, d318835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44991 q = 1) (hb : d318836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44991, d318836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44991, d318836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44992 q = 1) (hb : d318837 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44992, d318837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44992, d318837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104943 (p : Pattern) (ha : d44998 p = 1) (hb : d318843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1084 q = 1) (hb : d52665 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44996 q = 1) (hb : d318841 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, d318841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44996, d318841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44880 q = 1) (hb : d263912 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d44881 q = 1) (hb : d318726 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d15 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44882 q = 1) (hb : d318727 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44882, d318727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44882, d318727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44997 q = 1) (hb : d318842 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44997, d318842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44997, d318842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16 q = 1) (hb : d51868 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44883 q = 1) (hb : d318728 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44883, d318728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44883, d318728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44998 q = 1) (hb : d318843 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44998, d318843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44998, d318843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro104944 (p : Pattern) (ha : d45004 p = 1) (hb : d318849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d318844 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d318845 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d318846 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d318846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d318846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45002 q = 1) (hb : d318847 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d318847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45002, d318847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45003 q = 1) (hb : d318848 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d318848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45003, d318848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44888 q = 1) (hb : d318733 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, d318733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44888, d318733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44889 q = 1) (hb : d318734 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, d318734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44889, d318734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45004 q = 1) (hb : d318849 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45004, d318849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45004, d318849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro104945 (p : Pattern) (ha : d45012 p = 1) (hb : d318857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45010 q = 1) (hb : d318855 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d318855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45010, d318855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45011 q = 1) (hb : d318856 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d318856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45011, d318856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d51874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45012 q = 1) (hb : d318857 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45012, d318857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45012, d318857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104946 (p : Pattern) (ha : d45018 p = 1) (hb : d318863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45005 q = 1) (hb : d318850 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45005, d318850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104944 q ha hb
    | true =>
      simp only [d45005, d318850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45006 q = 1) (hb : d318851 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45006, d318851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45006, d318851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45007 q = 1) (hb : d318852 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45007, d318852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45007, d318852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45008 q = 1) (hb : d318853 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45008, d318853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45008, d318853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44891 q = 1) (hb : d318736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104925 q ha hb
    | true =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44892 q = 1) (hb : d318737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44893 q = 1) (hb : d318738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44893, d318738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44893, d318738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44894 q = 1) (hb : d318739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44894, d318739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44894, d318739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45009 q = 1) (hb : d318854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45009, d318854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45009, d318854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45013 q = 1) (hb : d318858 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
    | true =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45014 q = 1) (hb : d318859 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45015 q = 1) (hb : d318860 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d318860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d318860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45016 q = 1) (hb : d318861 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d318861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45016, d318861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45017 q = 1) (hb : d318862 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45017, d318862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45017, d318862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45018 q = 1) (hb : d318863 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45018, d318863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45018, d318863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104947 (p : Pattern) (ha : d45024 p = 1) (hb : d318869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45019 q = 1) (hb : d318864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d318864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104946 q ha hb
    | true =>
      simp only [d45019, d318864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104926 q ha hb
  have h2 (q : Pattern) (ha : d45020 q = 1) (hb : d318865 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d318865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d318865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45021 q = 1) (hb : d318866 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d318866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d318866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44897 q = 1) (hb : d318742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104926 q ha hb
    | true =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d44898 q = 1) (hb : d318743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44899 q = 1) (hb : d318744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45022 q = 1) (hb : d318867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d318867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45022, d318867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44900 q = 1) (hb : d318745 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44900, d318745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44900, d318745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45023 q = 1) (hb : d318868 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45023, d318868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45023, d318868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45024 q = 1) (hb : d318869 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45024, d318869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45024, d318869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro104948 (p : Pattern) (ha : d45030 p = 1) (hb : d318875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45025 q = 1) (hb : d318870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45025, d318870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104947 q ha hb
    | true =>
      simp only [d45025, d318870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45026 q = 1) (hb : d318871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45026, d318871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45026, d318871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45027 q = 1) (hb : d318872 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45027, d318872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45027, d318872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45028 q = 1) (hb : d318873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45028, d318873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45028, d318873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45029 q = 1) (hb : d318874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45029, d318874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45029, d318874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45030 q = 1) (hb : d318875 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45030, d318875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45030, d318875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104949 (p : Pattern) (ha : d45065 p = 1) (hb : d318881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45062 q = 1) (hb : d318878 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45062, d318878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45062, d318878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45063 q = 1) (hb : d318879 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45063, d318879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45063, d318879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45064 q = 1) (hb : d318880 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45064, d318880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45064, d318880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45065 q = 1) (hb : d318881 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45065, d318881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45065, d318881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104950 (p : Pattern) (ha : d318887 p = 1) (hb : d322048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44986 q = 1) (hb : d318831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44986, d318831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104941 q ha hb
    | true =>
      simp only [d44986, d318831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d44987 q = 1) (hb : d318832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44987, d318832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44987, d318832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44988 q = 1) (hb : d318833 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44988, d318833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44988, d318833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44989 q = 1) (hb : d318834 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44989, d318834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44989, d318834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44993 q = 1) (hb : d318838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44993, d318838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104942 q ha hb
    | true =>
      simp only [d44993, d318838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d44994 q = 1) (hb : d318839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44994, d318839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44994, d318839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44995 q = 1) (hb : d318840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44995, d318840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44995, d318840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45031 q = 1) (hb : d318876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45031, d318876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104948 q ha hb
    | true =>
      simp only [d45031, d318876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d318877 q = 1) (hb : d322044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318877, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d318877, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d45066 q = 1) (hb : d318882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45066, d318882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104949 q ha hb
    | true =>
      simp only [d45066, d318882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45067 q = 1) (hb : d318883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45067, d318883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45067, d318883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d318884 q = 1) (hb : d322045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318884, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318884, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d318885 q = 1) (hb : d322046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318885, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d318885, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d318886 q = 1) (hb : d322047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318886, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318886, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d318887 q = 1) (hb : d322048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318887, d322048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318887, d322048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104951 (p : Pattern) (ha : d45072 p = 1) (hb : d318888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d318750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44906 q = 1) (hb : d318751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d318751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44906, d318751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44984 q = 1) (hb : d318829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44984, d318829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44984, d318829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45072 q = 1) (hb : d318888 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45072, d318888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45072, d318888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104952 (p : Pattern) (ha : d45077 p = 1) (hb : d318893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d318750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d318750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44990 q = 1) (hb : d318835 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44990, d318835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44990, d318835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44991 q = 1) (hb : d318836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44991, d318836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44991, d318836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45077 q = 1) (hb : d318893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45077, d318893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45077, d318893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104953 (p : Pattern) (ha : d45081 p = 1) (hb : d318897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45025 q = 1) (hb : d318870 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45025, d318870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104947 q ha hb
    | true =>
      simp only [d45025, d318870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45026 q = 1) (hb : d318871 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45026, d318871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45026, d318871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45027 q = 1) (hb : d318872 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45027, d318872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45027, d318872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45028 q = 1) (hb : d318873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45028, d318873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45028, d318873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45029 q = 1) (hb : d318874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45029, d318874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45029, d318874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45081 q = 1) (hb : d318897 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45081, d318897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45081, d318897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104954 (p : Pattern) (ha : d45086 p = 1) (hb : d318900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104927 q ha hb
    | true =>
      simp only [d44903, d318748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d318749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45062 q = 1) (hb : d318878 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45062, d318878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45062, d318878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45063 q = 1) (hb : d318879 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45063, d318879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45063, d318879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45064 q = 1) (hb : d318880 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45064, d318880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45064, d318880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45086 q = 1) (hb : d318900 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45086, d318900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45086, d318900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104955 (p : Pattern) (ha : d318906 p = 1) (hb : d322053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44986 q = 1) (hb : d318831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44986, d318831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104941 q ha hb
    | true =>
      simp only [d44986, d318831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d44987 q = 1) (hb : d318832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44987, d318832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44987, d318832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44988 q = 1) (hb : d318833 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44988, d318833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44988, d318833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44989 q = 1) (hb : d318834 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44989, d318834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44989, d318834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44993 q = 1) (hb : d318838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44993, d318838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104942 q ha hb
    | true =>
      simp only [d44993, d318838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d44994 q = 1) (hb : d318839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44994, d318839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44994, d318839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44995 q = 1) (hb : d318840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44995, d318840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44995, d318840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45031 q = 1) (hb : d318876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45031, d318876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104948 q ha hb
    | true =>
      simp only [d45031, d318876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d318877 q = 1) (hb : d322044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318877, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d318877, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d45066 q = 1) (hb : d318882 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45066, d318882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104949 q ha hb
    | true =>
      simp only [d45066, d318882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45067 q = 1) (hb : d318883 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45067, d318883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45067, d318883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d318884 q = 1) (hb : d322045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318884, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318884, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d318885 q = 1) (hb : d322046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318885, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d318885, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d318886 q = 1) (hb : d322047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318886, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318886, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45073 q = 1) (hb : d318889 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45073, d318889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104951 q ha hb
    | true =>
      simp only [d45073, d318889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d45074 q = 1) (hb : d318890 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45074, d318890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45074, d318890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45075 q = 1) (hb : d318891 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45075, d318891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d45075, d318891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d45076 q = 1) (hb : d318892 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45076, d318892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45076, d318892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d45078 q = 1) (hb : d318894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45078, d318894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104952 q ha hb
    | true =>
      simp only [d45078, d318894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d45079 q = 1) (hb : d318895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45079, d318895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45079, d318895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d45080 q = 1) (hb : d318896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45080, d318896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45080, d318896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d45082 q = 1) (hb : d318898 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45082, d318898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104953 q ha hb
    | true =>
      simp only [d45082, d318898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104930 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d318899 q = 1) (hb : d322049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318899, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d318899, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d45087 q = 1) (hb : d318901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45087, d318901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104954 q ha hb
    | true =>
      simp only [d45087, d318901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d45088 q = 1) (hb : d318902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45088, d318902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d45088, d318902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d318903 q = 1) (hb : d322050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318903, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d318903, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d318904 q = 1) (hb : d322051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318904, d322051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d318904, d322051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d318905 q = 1) (hb : d322052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318905, d322052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d318905, d322052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d318906 q = 1) (hb : d322053 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318906, d322053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318906, d322053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro104956 (p : Pattern) (ha : d318915 p = 1) (hb : d322060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45082 q = 1) (hb : d318898 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45082, d318898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104953 q ha hb
    | true =>
      simp only [d45082, d318898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104930 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318899 q = 1) (hb : d322049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318899, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318899, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d45087 q = 1) (hb : d318901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45087, d318901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104954 q ha hb
    | true =>
      simp only [d45087, d318901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45088 q = 1) (hb : d318902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45088, d318902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45088, d318902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318903 q = 1) (hb : d322050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318903, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318903, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d318913 q = 1) (hb : d322058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318913, d322058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318913, d322058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318914 q = 1) (hb : d322059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318914, d322059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318914, d322059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318915 q = 1) (hb : d322060 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318915, d322060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318915, d322060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104957 (p : Pattern) (ha : d45117 p = 1) (hb : d318931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45107 q = 1) (hb : d318921 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45107, d318921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45107, d318921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104944 q ha hb
  have h2 (q : Pattern) (ha : d45005 q = 1) (hb : d318850 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45005, d318850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104944 q ha hb
    | true =>
      simp only [d45005, d318850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45108 q = 1) (hb : d318922 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45108, d318922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45108, d318922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45006 q = 1) (hb : d318851 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45006, d318851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45006, d318851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45109 q = 1) (hb : d318923 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45109, d318923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45109, d318923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45110 q = 1) (hb : d318924 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45110, d318924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45110, d318924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44934 q = 1) (hb : d318779 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44934, d318779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44934, d318779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104925 q ha hb
  have h8 (q : Pattern) (ha : d44891 q = 1) (hb : d318736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104925 q ha hb
    | true =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44935 q = 1) (hb : d318780 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44935, d318780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44935, d318780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44892 q = 1) (hb : d318737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44936 q = 1) (hb : d318781 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44936, d318781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44936, d318781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44937 q = 1) (hb : d318782 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44937, d318782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44937, d318782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45111 q = 1) (hb : d318925 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45111, d318925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45111, d318925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45112 q = 1) (hb : d318926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45112, d318926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45112, d318926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
  have h15 (q : Pattern) (ha : d45013 q = 1) (hb : d318858 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
    | true =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45113 q = 1) (hb : d318927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45113, d318927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45113, d318927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45014 q = 1) (hb : d318859 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45114 q = 1) (hb : d318928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45114, d318928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45114, d318928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45115 q = 1) (hb : d318929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45115, d318929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d45115, d318929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d45116 q = 1) (hb : d318930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45116, d318930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45116, d318930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d45117 q = 1) (hb : d318931 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45117, d318931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45117, d318931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro104958 (p : Pattern) (ha : d45123 p = 1) (hb : d318937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45118 q = 1) (hb : d318932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45118, d318932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104957 q ha hb
    | true =>
      simp only [d45118, d318932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104933 q ha hb
  have h2 (q : Pattern) (ha : d45119 q = 1) (hb : d318933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45119, d318933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45119, d318933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45120 q = 1) (hb : d318934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45120, d318934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45120, d318934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44940 q = 1) (hb : d318785 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104933 q ha hb
    | true =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d44941 q = 1) (hb : d318786 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44942 q = 1) (hb : d318787 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45121 q = 1) (hb : d318935 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45121, d318935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45121, d318935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44943 q = 1) (hb : d318788 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44943, d318788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44943, d318788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45122 q = 1) (hb : d318936 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45122, d318936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45122, d318936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45123 q = 1) (hb : d318937 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45123, d318937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45123, d318937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro104959 (p : Pattern) (ha : d45129 p = 1) (hb : d318943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45124 q = 1) (hb : d318938 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45124, d318938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104958 q ha hb
    | true =>
      simp only [d45124, d318938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45125 q = 1) (hb : d318939 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45125, d318939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45125, d318939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44946 q = 1) (hb : d318791 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d318791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104934 q ha hb
    | true =>
      simp only [d44946, d318791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44947 q = 1) (hb : d318792 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d318792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d318792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45126 q = 1) (hb : d318940 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45126, d318940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45126, d318940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45127 q = 1) (hb : d318941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45127, d318941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45127, d318941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45128 q = 1) (hb : d318942 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45128, d318942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45128, d318942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45129 q = 1) (hb : d318943 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45129, d318943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45129, d318943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104960 (p : Pattern) (ha : d45154 p = 1) (hb : d318949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44946 q = 1) (hb : d318791 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d318791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104934 q ha hb
    | true =>
      simp only [d44946, d318791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44947 q = 1) (hb : d318792 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d318792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d318792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45151 q = 1) (hb : d318946 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45151, d318946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45151, d318946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45152 q = 1) (hb : d318947 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45152, d318947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45152, d318947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45153 q = 1) (hb : d318948 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45153, d318948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45153, d318948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45154 q = 1) (hb : d318949 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45154, d318949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45154, d318949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104961 (p : Pattern) (ha : d318955 p = 1) (hb : d322070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45130 q = 1) (hb : d318944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45130, d318944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104959 q ha hb
    | true =>
      simp only [d45130, d318944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104935 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318945 q = 1) (hb : d322066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318945, d322066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318945, d322066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d45155 q = 1) (hb : d318950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45155, d318950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104960 q ha hb
    | true =>
      simp only [d45155, d318950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45156 q = 1) (hb : d318951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45156, d318951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45156, d318951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318952 q = 1) (hb : d322067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318952, d322067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318952, d322067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d318953 q = 1) (hb : d322068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318953, d322068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318953, d322068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318954 q = 1) (hb : d322069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318954, d322069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318954, d322069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318955 q = 1) (hb : d322070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318955, d322070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318955, d322070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro104962 (p : Pattern) (ha : d318961 p = 1) (hb : d322076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44974 q = 1) (hb : d318819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44974, d318819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44974, d318819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104938 q ha hb
  have h2 (q : Pattern) (ha : d44975 q = 1) (hb : d318820 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44975, d318820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44975, d318820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44981 q = 1) (hb : d318826 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d318826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104938 q ha hb
    | true =>
      simp only [d44981, d318826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104939 q ha hb
  have h4 (q : Pattern) (ha : d44982 q = 1) (hb : d318827 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d318827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44982, d318827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44983 q = 1) (hb : d318828 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44983, d318828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44983, d318828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318907 q = 1) (hb : d322054 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318907, d322054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104950 q ha hb
    | true =>
      simp only [d318907, d322054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104955 q ha hb
  have h7 (q : Pattern) (ha : d45095 q = 1) (hb : d318909 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45095, d318909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104940 q ha hb
    | true =>
      simp only [d45095, d318909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d318910 q = 1) (hb : d322055 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318910, d322055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318910, d322055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d318911 q = 1) (hb : d322056 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318911, d322056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318911, d322056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d318912 q = 1) (hb : d322057 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318912, d322057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d318912, d322057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d318916 q = 1) (hb : d322061 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318916, d322061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318916, d322061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104956 q ha hb
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
  have h13 (q : Pattern) (ha : d318917 q = 1) (hb : d322062 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318917, d322062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d318917, d322062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d318918 q = 1) (hb : d322063 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318918, d322063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318918, d322063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d318919 q = 1) (hb : d322064 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318919, d322064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d318919, d322064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d318920 q = 1) (hb : d322065 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318920, d322065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318920, d322065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d318956 q = 1) (hb : d322071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318956, d322071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318956, d322071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104961 q ha hb
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
  have h19 (q : Pattern) (ha : d318957 q = 1) (hb : d322072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318957, d322072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d318957, d322072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d318958 q = 1) (hb : d322073 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318958, d322073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d318958, d322073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d318959 q = 1) (hb : d322074 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318959, d322074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d318959, d322074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d318960 q = 1) (hb : d322075 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318960, d322075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d318960, d322075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d318961 q = 1) (hb : d322076 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d318961, d322076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d318961, d322076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro104963 (p : Pattern) (ha : d318967 p = 1) (hb : d322082 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d318809 q = 1) (hb : d322039 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318809, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318809, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104937 q ha hb
  have h6 (q : Pattern) (ha : d318810 q = 1) (hb : d322040 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318810, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318810, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318811 q = 1) (hb : d322041 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318811, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318811, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318812 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318812, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318812, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318813 q = 1) (hb : d322043 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318813, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318813, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318962 q = 1) (hb : d322077 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318962, d322077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318962, d322077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104962 q ha hb
  have h11 (q : Pattern) (ha : d318963 q = 1) (hb : d322078 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318963, d322078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318963, d322078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d318964 q = 1) (hb : d322079 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318964, d322079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318964, d322079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d318965 q = 1) (hb : d322080 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318965, d322080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318965, d322080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d318966 q = 1) (hb : d322081 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318966, d322081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318966, d322081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d318967 q = 1) (hb : d322082 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318967, d322082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318967, d322082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro104964 (p : Pattern) (ha : d45175 p = 1) (hb : d318970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45019 q = 1) (hb : d318864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d318864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104946 q ha hb
    | true =>
      simp only [d45019, d318864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104926 q ha hb
  have h2 (q : Pattern) (ha : d45020 q = 1) (hb : d318865 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d318865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d318865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45021 q = 1) (hb : d318866 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d318866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d318866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44897 q = 1) (hb : d318742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104926 q ha hb
    | true =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d44898 q = 1) (hb : d318743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44899 q = 1) (hb : d318744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45022 q = 1) (hb : d318867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d318867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45022, d318867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45173 q = 1) (hb : d318968 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45173, d318968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45173, d318968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45174 q = 1) (hb : d318969 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45174, d318969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45174, d318969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45175 q = 1) (hb : d318970 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45175, d318970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45175, d318970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro104965 (p : Pattern) (ha : d45179 p = 1) (hb : d318974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44897 q = 1) (hb : d318742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104926 q ha hb
    | true =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d44898 q = 1) (hb : d318743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44899 q = 1) (hb : d318744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45173 q = 1) (hb : d318968 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45173, d318968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45173, d318968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45178 q = 1) (hb : d318973 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45178, d318973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45178, d318973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45179 q = 1) (hb : d318974 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45179, d318974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45179, d318974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104966 (p : Pattern) (ha : d45185 p = 1) (hb : d318980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318977 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d318978 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d318978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d318978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45184 q = 1) (hb : d318979 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45184, d318979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45184, d318979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45185 q = 1) (hb : d318980 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45185, d318980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45185, d318980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104967 (p : Pattern) (ha : d45189 p = 1) (hb : d318984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d318982 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d318982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d318982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45188 q = 1) (hb : d318983 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45188, d318983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45188, d318983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45189 q = 1) (hb : d318984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45189, d318984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45189, d318984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104968 (p : Pattern) (ha : d45195 p = 1) (hb : d318990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d318985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104966 q ha hb
    | true =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104967 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d318986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d318986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d318986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d318987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d318987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d318987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d318988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d318988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d318988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d318989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d318989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d318989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45195 q = 1) (hb : d318990 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45195, d318990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45195, d318990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104969 (p : Pattern) (ha : d45198 p = 1) (hb : d318993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318977 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d318978 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d318978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d318978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45184 q = 1) (hb : d318979 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45184, d318979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45184, d318979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45198 q = 1) (hb : d318993 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45198, d318993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45198, d318993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104970 (p : Pattern) (ha : d45199 p = 1) (hb : d318994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d318982 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d318982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d318982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45188 q = 1) (hb : d318983 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45188, d318983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45188, d318983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45199 q = 1) (hb : d318994 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45199, d318994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45199, d318994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104971 (p : Pattern) (ha : d45205 p = 1) (hb : d319000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d318985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104966 q ha hb
    | true =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104967 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d318986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d318986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d318986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d318987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d318987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d318987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d318988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d318988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d318988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d318989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d318989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d318989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45200 q = 1) (hb : d318995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d318995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104969 q ha hb
    | true =>
      simp only [d45200, d318995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104970 q ha hb
  have h7 (q : Pattern) (ha : d45201 q = 1) (hb : d318996 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d318996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45201, d318996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45202 q = 1) (hb : d318997 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d318997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45202, d318997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45203 q = 1) (hb : d318998 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d318998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45203, d318998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45204 q = 1) (hb : d318999 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d318999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45204, d318999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45205 q = 1) (hb : d319000 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45205, d319000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45205, d319000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104972 (p : Pattern) (ha : d45363 p = 1) (hb : d319110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d318985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104966 q ha hb
    | true =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104967 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d318986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d318986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d318986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d318987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d318987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d318987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d318988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d318988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d318988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d318989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d318989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d318989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45358 q = 1) (hb : d319105 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45358, d319105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104967 q ha hb
    | true =>
      simp only [d45358, d319105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45359 q = 1) (hb : d319106 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45359, d319106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45359, d319106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45360 q = 1) (hb : d319107 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45360, d319107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45360, d319107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45361 q = 1) (hb : d319108 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45361, d319108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45361, d319108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45362 q = 1) (hb : d319109 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45362, d319109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45362, d319109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45363 q = 1) (hb : d319110 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45363, d319110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45363, d319110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104973 (p : Pattern) (ha : d45369 p = 1) (hb : d319116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45358 q = 1) (hb : d319105 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45358, d319105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104967 q ha hb
    | true =>
      simp only [d45358, d319105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45359 q = 1) (hb : d319106 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45359, d319106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45359, d319106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45360 q = 1) (hb : d319107 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45360, d319107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45360, d319107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45361 q = 1) (hb : d319108 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45361, d319108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45361, d319108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45362 q = 1) (hb : d319109 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45362, d319109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45362, d319109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45364 q = 1) (hb : d319111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45364, d319111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104970 q ha hb
    | true =>
      simp only [d45364, d319111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45365 q = 1) (hb : d319112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45365, d319112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45365, d319112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45366 q = 1) (hb : d319113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45366, d319113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45366, d319113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45367 q = 1) (hb : d319114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45367, d319114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45367, d319114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45368 q = 1) (hb : d319115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45368, d319115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45368, d319115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45369 q = 1) (hb : d319116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45369, d319116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45369, d319116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104974 (p : Pattern) (ha : d45378 p = 1) (hb : d319125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45364 q = 1) (hb : d319111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45364, d319111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104970 q ha hb
    | true =>
      simp only [d45364, d319111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45365 q = 1) (hb : d319112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45365, d319112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45365, d319112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45366 q = 1) (hb : d319113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45366, d319113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45366, d319113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45367 q = 1) (hb : d319114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45367, d319114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45367, d319114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45368 q = 1) (hb : d319115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45368, d319115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45368, d319115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45378 q = 1) (hb : d319125 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45378, d319125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45378, d319125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104975 (p : Pattern) (ha : d45421 p = 1) (hb : d319168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44940 q = 1) (hb : d318785 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104933 q ha hb
    | true =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d44941 q = 1) (hb : d318786 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44942 q = 1) (hb : d318787 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45411 q = 1) (hb : d319158 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45411, d319158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45411, d319158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45420 q = 1) (hb : d319167 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45420, d319167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45420, d319167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45421 q = 1) (hb : d319168 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45421, d319168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45421, d319168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104976 (p : Pattern) (ha : d45477 p = 1) (hb : d319179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45422 q = 1) (hb : d319169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45422, d319169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104975 q ha hb
    | true =>
      simp only [d45422, d319169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45423 q = 1) (hb : d319170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45423, d319170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45423, d319170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45474 q = 1) (hb : d319176 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45474, d319176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45474, d319176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45475 q = 1) (hb : d319177 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45475, d319177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45475, d319177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45476 q = 1) (hb : d319178 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45476, d319178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45476, d319178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45477 q = 1) (hb : d319179 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45477, d319179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45477, d319179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104977 (p : Pattern) (ha : d45483 p = 1) (hb : d319198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45478 q = 1) (hb : d319193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45478, d319193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104976 q ha hb
    | true =>
      simp only [d45478, d319193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45479 q = 1) (hb : d319194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45479, d319194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45479, d319194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45480 q = 1) (hb : d319195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45480, d319195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45480, d319195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45481 q = 1) (hb : d319196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45481, d319196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45481, d319196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45482 q = 1) (hb : d319197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45482, d319197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45482, d319197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45483 q = 1) (hb : d319198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45483, d319198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45483, d319198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104978 (p : Pattern) (ha : d45210 p = 1) (hb : d319005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318977 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d318978 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d318978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d318978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45209 q = 1) (hb : d319004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45209, d319004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45209, d319004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45210 q = 1) (hb : d319005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45210, d319005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45210, d319005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104979 (p : Pattern) (ha : d45212 p = 1) (hb : d319007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d318982 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d318982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d318982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45211 q = 1) (hb : d319006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45211, d319006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45211, d319006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45212 q = 1) (hb : d319007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45212, d319007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45212, d319007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104980 (p : Pattern) (ha : d45219 p = 1) (hb : d319014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318977 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45217 q = 1) (hb : d319012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45217, d319012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45217, d319012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45218 q = 1) (hb : d319013 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45218, d319013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45218, d319013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45219 q = 1) (hb : d319014 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45219, d319014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45219, d319014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104981 (p : Pattern) (ha : d45222 p = 1) (hb : d319017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45220 q = 1) (hb : d319015 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45220, d319015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45220, d319015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45221 q = 1) (hb : d319016 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45221, d319016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45221, d319016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45222 q = 1) (hb : d319017 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45222, d319017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45222, d319017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104982 (p : Pattern) (ha : d45227 p = 1) (hb : d319022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44880 q = 1) (hb : d263912 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44881 q = 1) (hb : d318726 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44882 q = 1) (hb : d318727 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44882, d318727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44882, d318727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45226 q = 1) (hb : d319021 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45226, d319021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45226, d319021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45227 q = 1) (hb : d319022 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45227, d319022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45227, d319022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104983 (p : Pattern) (ha : d45234 p = 1) (hb : d319029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1084 q = 1) (hb : d52665 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44996 q = 1) (hb : d318841 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, d318841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44996, d318841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44880 q = 1) (hb : d263912 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d44881 q = 1) (hb : d318726 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d45231 q = 1) (hb : d319026 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45231, d319026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45231, d319026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45232 q = 1) (hb : d319027 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45232, d319027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45232, d319027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16 q = 1) (hb : d51868 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45233 q = 1) (hb : d319028 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45233, d319028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45233, d319028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45234 q = 1) (hb : d319029 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45234, d319029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45234, d319029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro104984 (p : Pattern) (ha : d45240 p = 1) (hb : d319035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45228 q = 1) (hb : d319023 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45228, d319023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45228, d319023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45229 q = 1) (hb : d319024 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45229, d319024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45229, d319024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44999 q = 1) (hb : d318844 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45000 q = 1) (hb : d318845 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45230 q = 1) (hb : d319025 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45230, d319025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45230, d319025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45235 q = 1) (hb : d319030 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45235, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104983 q ha hb
    | true =>
      simp only [d45235, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45236 q = 1) (hb : d319031 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45236, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45236, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45237 q = 1) (hb : d319032 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45237, d319032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45237, d319032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45238 q = 1) (hb : d319033 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45238, d319033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45238, d319033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45239 q = 1) (hb : d319034 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45239, d319034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45239, d319034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45001 q = 1) (hb : d318846 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d318846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45001, d318846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45002 q = 1) (hb : d318847 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d318847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45002, d318847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45003 q = 1) (hb : d318848 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d318848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d45003, d318848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d45240 q = 1) (hb : d319035 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45240, d319035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45240, d319035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104985 (p : Pattern) (ha : d45245 p = 1) (hb : d319040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d318844 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d318845 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d318846 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d318846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d318846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45002 q = 1) (hb : d318847 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d318847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45002, d318847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45003 q = 1) (hb : d318848 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d318848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45003, d318848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45010 q = 1) (hb : d318855 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d318855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45010, d318855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45011 q = 1) (hb : d318856 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d318856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45011, d318856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45245 q = 1) (hb : d319040 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45245, d319040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45245, d319040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro104986 (p : Pattern) (ha : d45253 p = 1) (hb : d319048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d318844 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d318845 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d318846 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d318846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d318846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45251 q = 1) (hb : d319046 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45251, d319046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45251, d319046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45252 q = 1) (hb : d319047 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45252, d319047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45252, d319047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45010 q = 1) (hb : d318855 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d318855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45010, d318855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45011 q = 1) (hb : d318856 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d318856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45011, d318856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45253 q = 1) (hb : d319048 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45253, d319048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45253, d319048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro104987 (p : Pattern) (ha : d45259 p = 1) (hb : d319054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45241 q = 1) (hb : d319036 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45241, d319036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104984 q ha hb
    | true =>
      simp only [d45241, d319036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45242 q = 1) (hb : d319037 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45242, d319037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45242, d319037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45243 q = 1) (hb : d319038 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45243, d319038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45243, d319038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45244 q = 1) (hb : d319039 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45244, d319039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45244, d319039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45246 q = 1) (hb : d319041 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45246, d319041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104985 q ha hb
    | true =>
      simp only [d45246, d319041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45247 q = 1) (hb : d319042 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45247, d319042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45247, d319042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45248 q = 1) (hb : d319043 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45248, d319043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45248, d319043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45249 q = 1) (hb : d319044 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45249, d319044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45249, d319044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45250 q = 1) (hb : d319045 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45250, d319045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45250, d319045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45254 q = 1) (hb : d319049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
    | true =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45255 q = 1) (hb : d319050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45256 q = 1) (hb : d319051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45256, d319051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45256, d319051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45257 q = 1) (hb : d319052 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45257, d319052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45257, d319052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45013 q = 1) (hb : d318858 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
    | true =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45014 q = 1) (hb : d318859 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45015 q = 1) (hb : d318860 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d318860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d318860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45016 q = 1) (hb : d318861 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d318861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45016, d318861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45258 q = 1) (hb : d319053 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45258, d319053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45258, d319053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45259 q = 1) (hb : d319054 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45259, d319054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45259, d319054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro104988 (p : Pattern) (ha : d45263 p = 1) (hb : d319058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45013 q = 1) (hb : d318858 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
    | true =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45014 q = 1) (hb : d318859 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45015 q = 1) (hb : d318860 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d318860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d318860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45016 q = 1) (hb : d318861 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d318861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45016, d318861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45017 q = 1) (hb : d318862 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45017, d318862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45017, d318862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45263 q = 1) (hb : d319058 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45263, d319058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45263, d319058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro104989 (p : Pattern) (ha : d45269 p = 1) (hb : d319064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45260 q = 1) (hb : d319055 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45260, d319055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104987 q ha hb
    | true =>
      simp only [d45260, d319055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104946 q ha hb
  have h2 (q : Pattern) (ha : d45261 q = 1) (hb : d319056 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45261, d319056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45261, d319056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45262 q = 1) (hb : d319057 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45262, d319057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45262, d319057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45264 q = 1) (hb : d319059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45264, d319059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104946 q ha hb
    | true =>
      simp only [d45264, d319059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104988 q ha hb
  have h5 (q : Pattern) (ha : d45265 q = 1) (hb : d319060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45265, d319060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45265, d319060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45266 q = 1) (hb : d319061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45266, d319061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45266, d319061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45267 q = 1) (hb : d319062 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45267, d319062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45267, d319062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45019 q = 1) (hb : d318864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d318864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104946 q ha hb
    | true =>
      simp only [d45019, d318864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104926 q ha hb
  have h9 (q : Pattern) (ha : d45020 q = 1) (hb : d318865 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d318865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d318865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45021 q = 1) (hb : d318866 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d318866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d318866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44897 q = 1) (hb : d318742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104926 q ha hb
    | true =>
      simp only [d44897, d318742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h12 (q : Pattern) (ha : d44898 q = 1) (hb : d318743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d318743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44899 q = 1) (hb : d318744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d318744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45022 q = 1) (hb : d318867 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d318867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45022, d318867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45268 q = 1) (hb : d319063 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45268, d319063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45268, d319063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45269 q = 1) (hb : d319064 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45269, d319064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45269, d319064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro104990 (p : Pattern) (ha : d45275 p = 1) (hb : d319070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45270 q = 1) (hb : d319065 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45270, d319065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104989 q ha hb
    | true =>
      simp only [d45270, d319065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45271 q = 1) (hb : d319066 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45271, d319066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45271, d319066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45272 q = 1) (hb : d319067 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45272, d319067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45272, d319067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45273 q = 1) (hb : d319068 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45273, d319068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45273, d319068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45274 q = 1) (hb : d319069 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45274, d319069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45274, d319069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45275 q = 1) (hb : d319070 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45275, d319070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45275, d319070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro104991 (p : Pattern) (ha : d45326 p = 1) (hb : d319076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45323 q = 1) (hb : d319073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45323, d319073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45323, d319073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45324 q = 1) (hb : d319074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45324, d319074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45324, d319074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45325 q = 1) (hb : d319075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45325, d319075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45325, d319075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45326 q = 1) (hb : d319076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45326, d319076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45326, d319076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro104992 (p : Pattern) (ha : d319082 p = 1) (hb : d322087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45213 q = 1) (hb : d319008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45213, d319008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104978 q ha hb
    | true =>
      simp only [d45213, d319008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104979 q ha hb
  have h2 (q : Pattern) (ha : d45214 q = 1) (hb : d319009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45214, d319009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45214, d319009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45215 q = 1) (hb : d319010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45215, d319010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45215, d319010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45216 q = 1) (hb : d319011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45216, d319011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45216, d319011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45223 q = 1) (hb : d319018 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45223, d319018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104980 q ha hb
    | true =>
      simp only [d45223, d319018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104981 q ha hb
  have h6 (q : Pattern) (ha : d45224 q = 1) (hb : d319019 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45224, d319019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45224, d319019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45225 q = 1) (hb : d319020 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45225, d319020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45225, d319020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45276 q = 1) (hb : d319071 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45276, d319071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104990 q ha hb
    | true =>
      simp only [d45276, d319071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104966 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d318985 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d319072 q = 1) (hb : d322083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319072, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d319072, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d45327 q = 1) (hb : d319077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45327, d319077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104991 q ha hb
    | true =>
      simp only [d45327, d319077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45328 q = 1) (hb : d319078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45328, d319078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45328, d319078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d319079 q = 1) (hb : d322084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319079, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319079, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319080 q = 1) (hb : d322085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319080, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319080, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319081 q = 1) (hb : d322086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319081, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319081, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d319082 q = 1) (hb : d322087 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319082, d322087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319082, d322087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro104993 (p : Pattern) (ha : d45333 p = 1) (hb : d319083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318977 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d318978 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d318978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d318978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45209 q = 1) (hb : d319004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45209, d319004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45209, d319004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45333 q = 1) (hb : d319083 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45333, d319083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45333, d319083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104994 (p : Pattern) (ha : d45334 p = 1) (hb : d319084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d318982 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d318982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d318982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45211 q = 1) (hb : d319006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45211, d319006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45211, d319006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45334 q = 1) (hb : d319084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45334, d319084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45334, d319084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104995 (p : Pattern) (ha : d45339 p = 1) (hb : d319089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318977 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d318977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45217 q = 1) (hb : d319012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45217, d319012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45217, d319012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45218 q = 1) (hb : d319013 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45218, d319013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45218, d319013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45339 q = 1) (hb : d319089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45339, d319089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45339, d319089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104996 (p : Pattern) (ha : d45340 p = 1) (hb : d319090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318975 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104965 q ha hb
    | true =>
      simp only [d45180, d318975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318976 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d318976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d318981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45220 q = 1) (hb : d319015 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45220, d319015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45220, d319015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45221 q = 1) (hb : d319016 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45221, d319016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45221, d319016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45340 q = 1) (hb : d319090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45340, d319090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45340, d319090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104997 (p : Pattern) (ha : d45344 p = 1) (hb : d319094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45270 q = 1) (hb : d319065 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45270, d319065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104989 q ha hb
    | true =>
      simp only [d45270, d319065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45271 q = 1) (hb : d319066 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45271, d319066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45271, d319066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45272 q = 1) (hb : d319067 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45272, d319067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45272, d319067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45273 q = 1) (hb : d319068 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45273, d319068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45273, d319068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45274 q = 1) (hb : d319069 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45274, d319069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45274, d319069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45344 q = 1) (hb : d319094 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45344, d319094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45344, d319094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro104998 (p : Pattern) (ha : d45350 p = 1) (hb : d319097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318971 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104964 q ha hb
    | true =>
      simp only [d45176, d318971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318972 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d318972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45323 q = 1) (hb : d319073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45323, d319073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45323, d319073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45324 q = 1) (hb : d319074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45324, d319074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45324, d319074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45325 q = 1) (hb : d319075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45325, d319075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45325, d319075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45350 q = 1) (hb : d319097 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45350, d319097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45350, d319097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro104999 (p : Pattern) (ha : d319103 p = 1) (hb : d322092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45213 q = 1) (hb : d319008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45213, d319008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104978 q ha hb
    | true =>
      simp only [d45213, d319008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104979 q ha hb
  have h2 (q : Pattern) (ha : d45214 q = 1) (hb : d319009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45214, d319009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45214, d319009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45215 q = 1) (hb : d319010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45215, d319010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45215, d319010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45216 q = 1) (hb : d319011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45216, d319011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45216, d319011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45223 q = 1) (hb : d319018 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45223, d319018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104980 q ha hb
    | true =>
      simp only [d45223, d319018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104981 q ha hb
  have h6 (q : Pattern) (ha : d45224 q = 1) (hb : d319019 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45224, d319019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45224, d319019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45225 q = 1) (hb : d319020 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45225, d319020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45225, d319020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45276 q = 1) (hb : d319071 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45276, d319071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104990 q ha hb
    | true =>
      simp only [d45276, d319071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104966 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d318985 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d319072 q = 1) (hb : d322083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319072, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d319072, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d45327 q = 1) (hb : d319077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45327, d319077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104991 q ha hb
    | true =>
      simp only [d45327, d319077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45328 q = 1) (hb : d319078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45328, d319078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45328, d319078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d319079 q = 1) (hb : d322084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319079, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319079, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319080 q = 1) (hb : d322085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319080, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319080, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319081 q = 1) (hb : d322086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319081, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319081, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45335 q = 1) (hb : d319085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45335, d319085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104993 q ha hb
    | true =>
      simp only [d45335, d319085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104994 q ha hb
  have h17 (q : Pattern) (ha : d45336 q = 1) (hb : d319086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45336, d319086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45336, d319086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45337 q = 1) (hb : d319087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45337, d319087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d45337, d319087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d45338 q = 1) (hb : d319088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45338, d319088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45338, d319088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d45341 q = 1) (hb : d319091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45341, d319091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104995 q ha hb
    | true =>
      simp only [d45341, d319091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104996 q ha hb
  have h21 (q : Pattern) (ha : d45342 q = 1) (hb : d319092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45342, d319092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45342, d319092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d45343 q = 1) (hb : d319093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45343, d319093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45343, d319093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d45345 q = 1) (hb : d319095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45345, d319095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104997 q ha hb
    | true =>
      simp only [d45345, d319095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104969 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d318995 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d319096 q = 1) (hb : d322088 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319096, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d319096, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d45351 q = 1) (hb : d319098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45351, d319098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104998 q ha hb
    | true =>
      simp only [d45351, d319098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d45352 q = 1) (hb : d319099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45352, d319099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d45352, d319099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d319100 q = 1) (hb : d322089 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319100, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d319100, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d319101 q = 1) (hb : d322090 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319101, d322090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d319101, d322090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d319102 q = 1) (hb : d322091 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319102, d322091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d319102, d322091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d319103 q = 1) (hb : d322092 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319103, d322092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319103, d322092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
end NetHack.Soko22Hazard87
